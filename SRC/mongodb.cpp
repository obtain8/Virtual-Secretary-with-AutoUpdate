#include "common.h"

//////////////////////////////////////////////////////////
/// MONGO DATABASE FUNCTIONS
//////////////////////////////////////////////////////////

#ifndef DISCARDMONGO
    #ifdef WIN32
        #include "mongo/MongoDBClient.h"
        #include "mongo/stdafx.h"

        #pragma comment(lib, "../SRC/mongo/mongoc-1.0.lib")
        #pragma comment(lib, "../SRC/mongo/bson-1.0.lib")
    #else
        // #include <mongo/MongoDBClient.h>
		#include "mongo/MongoDBClient.h"
    #endif

// #include <bson.h>
// #include <bcon.h>
// #include <mongoc.h>

#include "bson.h"
#include "bcon.h"
#include "mongoc.h"

static bool mongoInited = false;		// have we inited mongo overall
static bool mongoShutdown = false;
char* mongoBuffer = NULL;
char* mongodbparams;

// for script use
mongoc_client_t*		g_pClient = NULL;
mongoc_database_t*		g_pDatabase = NULL;
mongoc_collection_t*	g_pCollection = NULL;
// for file system use
mongoc_client_t*		g_filesysClient = NULL;
mongoc_database_t*		g_filesysDatabase = NULL;
mongoc_collection_t*	g_filesysCollection = NULL;

void ProtectNL(char* buffer) // save ascii \r\n in json
{
	char* at = buffer;
	while ((at = strchr(at,'\r')))
	{
		if (at[1] == '\n' ) 
		{
			*at++ = 0x7f;
			*at++ = 0x7f;
		}
	}
}

char* MongoCleanEscapes(char* to, char* at,int limit) 
{ // any sequence of \\\ means mongo added \\  and any freestanding \ means mongo added that
	// and 0x7f 0x7f is our own crnl tag
	*to = 0;
	char* start = to;
	if (!at || !*at) return to;
	// need to remove escapes we put there
	--at;
	while (*++at)
	{
		if (*at == 0x7f && at[1] == 0x7f) // own special CR NL coding
		{
			*to++ = '\r';
			*to++ = '\n';
			++at;
		}
		else if (*at == '\\') // remove backslashed "
		{
			*to++ = *++at;
		}
		else *to++ = *at;
		if ((to-start) >= limit) // too much, kill it
		{
			*to = 0;
			break;
		}
	}
	*to = 0;
	return start;
}

// connect to server, db, and collection
eReturnValue EstablishConnection(	const char* pStrSeverUri, // eg "mongodb://localhost:27017"
									const char* pStrDBName,   // eg "testMongo""testMongo"
									const char* pStrCollName, // eg "testCollection"
									const char* scriptFlag)
{
	if( ( pStrSeverUri == NULL ) || ( pStrDBName == NULL ) || ( pStrCollName == NULL ) ) return eReturnValue_WRONG_ARGUEMENTS;

	// Required to initialize libmongoc's internals
	if (!mongoInited) mongoc_init();
	mongoInited = true;

	// Create a new client instance (user/script or interal/filesystem)
	mongoc_client_t* myclient  = mongoc_client_new( pStrSeverUri );
	if( myclient == NULL ) return eReturnValue_DATABASE_OPEN_CLIENT_CONNECTION_FAILED;
	if (scriptFlag) g_pClient = myclient; 
	else g_filesysClient = myclient;

	// Get a handle on the database "db_name"
	mongoc_database_t* mydb = mongoc_client_get_database(myclient, pStrDBName);
	if( mydb == NULL ) return eReturnValue_DATABASE_GET_FAILED;
	if (scriptFlag) g_pDatabase = mydb; 
	else g_filesysDatabase = mydb;

	// Get a handle on the collection "coll_name"
	mongoc_collection_t* mycollect  = mongoc_client_get_collection(myclient, pStrDBName, pStrCollName);
	if( mycollect == NULL ) return eReturnValue_DATABASE_GET_COLLECTION_FAILED;
	if (scriptFlag) g_pCollection = mycollect; 
	else g_filesysCollection = mycollect;

	return eReturnValue_SUCCESS;
}

FunctionResult MongoClose(char* buffer)
{
	if (!buffer && !g_filesysClient) return FAILRULE_BIT; // filesys mongo not being used
	if (buffer && !g_pClient)
	{
		if (mongoShutdown) return FAILRULE_BIT;
		char* msg = "DB is not open\r\n";
		SetUserVariable((char*)"$$mongo_error",msg);	// pass message along the error
		Log(STDTRACELOG,msg);
		return FAILRULE_BIT;
	}

	// Release our handles and clean up libmongoc
	if (buffer)
	{
		if( g_pCollection != NULL ) mongoc_collection_destroy(g_pCollection);
		if( g_pDatabase != NULL ) mongoc_database_destroy(g_pDatabase);
		if( g_pClient != NULL ) mongoc_client_destroy(g_pClient);
		g_pCollection = NULL;
		g_pDatabase = NULL;
		g_pClient = NULL;
	}
	else {
		if( g_filesysCollection != NULL ) mongoc_collection_destroy(g_filesysCollection);
		if( g_filesysDatabase != NULL ) mongoc_database_destroy(g_filesysDatabase);
		if( g_pClient != NULL ) mongoc_client_destroy(g_filesysClient);
		g_filesysCollection = NULL;
		g_filesysDatabase =  NULL;
		g_filesysClient = NULL;
	}
	*currentFilename = 0;
	return (buffer == NULL) ? FAILRULE_BIT : NOPROBLEM_BIT; 
}

FunctionResult MongoInit(char* buffer)
{
	if ((buffer && g_pClient) || (!buffer && g_filesysClient))
	{
		char* msg = "DB is already opened\r\n";
		SetUserVariable((char*)"$$mongo_error",msg);	// pass message along the error
		Log(STDTRACELOG,msg);
 		return FAILRULE_BIT;
	}

    /* Make a connection to the database */
    eReturnValue  eRetVal = EstablishConnection(ARGUMENT(1), ARGUMENT(2), ARGUMENT(3),buffer); // server, dbname, collection
    if (eRetVal != eReturnValue_SUCCESS )
    {	
		char* msg = "DB opening error \r\n";
		SetUserVariable((char*)"$$mongo_error",msg);	// pass message along the error
        Log(STDTRACELOG, "Opening connection failed with error: %d",  eRetVal);
		if ((buffer && g_pClient) || (!buffer && g_filesysClient)) MongoClose(buffer);
		return FAILRULE_BIT;
	}
	return NOPROBLEM_BIT;
}

FunctionResult mongoGetDocument(char* key,char* buffer,int limit,bool user)
{
	if (*key == '"') // remove quotes
	{
		++key;
		size_t len = strlen(key);
		if (key[len-1] == '"') key[len-1] = 0;
	}
    mongoc_collection_t* collection = (user) ? g_pCollection : g_filesysCollection;
    if (!collection)
    {
        char* msg = "DB is not open\r\n";
        SetUserVariable((char*)"$$mongo_error",msg);
        Log(STDTRACELOG,msg);
        return FAILRULE_BIT;
    }
    
    char* mongoKeyValue = NULL;   // keyValue result string
    eReturnValue eRetVal = eReturnValue_SUCCESS;
    bson_t* pDoc = NULL;
    mongoc_cursor_t* psCursor = NULL;
    bson_t* psQuery = NULL;
    char* pStrTemp = NULL;
    do
    {
        if( collection == NULL )
        {
            eRetVal = eReturnValue_DATABASE_COLLECTION_INVALID;
            break;
        }
        
        psQuery = bson_new ();
        if( psQuery == NULL )
        {
            eRetVal = eReturnValue_DATABASE_QUERY_CREATION_FAILED;
            break;
        }
        
        BSON_APPEND_UTF8 ( psQuery, "KeyName", key );
        
        psCursor = mongoc_collection_find(collection, MONGOC_QUERY_NONE, 0, 0, 0, psQuery, NULL, NULL);
        if( psCursor == NULL )
        {
            eRetVal = eReturnValue_DATABASE_QUERY_FAILED;
            break;
        }
        
        while( mongoc_cursor_next (psCursor, (const bson_t **)&pDoc) )
        {
            if (pDoc != NULL)
            {
                pStrTemp = bson_as_json( pDoc, NULL );
                if( pStrTemp != NULL )
                {
                    char* at = strstr(pStrTemp,"KeyValue");
                    if (at) // point into the buffer to the get value
                    {
                        at += 8 + 5;
                        mongoKeyValue = at;
                        size_t len = strlen(at);
                        at[len-3] = 0;	// remove key data
                    }
                    break;
                }
            }
        }
    }while(false);
    
    FunctionResult result = NOPROBLEM_BIT;
    if (eRetVal != eReturnValue_SUCCESS)
    {
        char* msg = "Error while looking for document \r\n";
        SetUserVariable((char*)"$$mongo_error",msg);	// pass along the error
        Log(STDTRACELOG, "Find document failed with error: %d",  eRetVal);
        result = FAILRULE_BIT;
    }
    else if (mongoKeyValue) 
    {
        unsigned int remainingSize = (user) ? (currentOutputLimit - (buffer - currentOutputBase) - 1)
			: (userCacheSize - MAX_USERNAME);
		MongoCleanEscapes(buffer, mongoKeyValue,remainingSize);
    }
    else result = FAILRULE_BIT;
    
    if( pDoc != NULL ) bson_destroy( pDoc );
    if( psQuery != NULL ) bson_destroy( psQuery );
    if( psCursor != NULL ) mongoc_cursor_destroy( psCursor );
    return result;
}

FunctionResult mongoFindDocument(char* buffer) // from user not system
{
    unsigned int remainingSize = currentOutputLimit - (buffer - currentOutputBase) - 1;
	char* dot = strchr(ARGUMENT(1),'.');
	if (dot) *dot = 0;	 // terminate any suffix, not legal in mongo key
	FunctionResult result = mongoGetDocument(ARGUMENT(1),buffer,remainingSize,true);
	if (dot) *dot = '.';	 // terminate any suffix, not legal in mongo key
	return result;
}

FunctionResult mongoDeleteDocument(char* buffer) 
{
	char* dot = strchr(ARGUMENT(1),'.');
	if (dot) *dot = 0; // not allowed by mongo
    mongoc_collection_t* collection = (buffer) ? g_pCollection : g_filesysCollection;
    if (!collection)
    {
        char* msg = "DB is not open\r\n";
        SetUserVariable((char*)"$$mongo_error",msg);	// pass along the error
        Log(STDTRACELOG,msg);
        return FAILRULE_BIT;
    }
    
    /* delete document from the database */
    char* keyname = ARGUMENT(1); // name the key
    eReturnValue eRetVal = eReturnValue_SUCCESS;
    bson_t* pDoc = NULL;
    do
    {
        if( keyname == NULL )
        {
            eRetVal = eReturnValue_WRONG_ARGUEMENTS;
            break;
        }
        
        pDoc = bson_new();
        if( pDoc == NULL )
        {
            eRetVal = eReturnValue_DATABASE_DOCUMENT_CREATION_FAILED;
            break;
        }
        
        BSON_APPEND_UTF8 ( pDoc, "KeyName", keyname );
        
        bson_error_t sError;
        
        if (!mongoc_collection_remove(	collection, MONGOC_REMOVE_SINGLE_REMOVE, pDoc, NULL, &sError))
        {
            eRetVal = eReturnValue_DATABASE_DOCUMENT_DELETION_FAILED;
        }
    }while(false);
    
    if( pDoc != NULL ) bson_destroy( pDoc );
    
    if (eRetVal != eReturnValue_SUCCESS)
    {
        char* msg = "Error while insert document \r\n";
        SetUserVariable((char*)"$$mongo_error",msg);	// pass along the error
        Log(STDTRACELOG, "Delete document failed with error: %d",  eRetVal);
        return FAILRULE_BIT;
    }
    return NOPROBLEM_BIT;
}

static FunctionResult MongoUpsertDoc(bool user,char* keyname, char* value)
{// assumes mongo client and db set up - document is merely a json string ready to ship
	if( !keyname || !*keyname || !value) return FAILRULE_BIT;
	char* dot = strchr(keyname,'.');
	if (dot) *dot = 0; // not allowed by mongo
 
 	//  we output no text result
    mongoc_collection_t* collection = (user) ? g_pCollection : g_filesysCollection;
    if (!collection)
    {
        char* msg = "DB is not open\r\n";
        SetUserVariable((char*)"$$mongo_error",msg);    // pass along the error
        Log(STDTRACELOG,msg);
        return FAILRULE_BIT;
    }
    
    /* insert/update document to the database */
    FunctionResult result = FAILRULE_BIT;
    bson_error_t error;
    bson_oid_t oid;
    bson_t *doc = NULL;
    bson_t *update = NULL;
    bson_t *query = NULL;
    bson_oid_init (&oid, NULL);
    query = BCON_NEW ("KeyName", BCON_UTF8 (keyname));
    update = BCON_NEW ("$set", "{", "KeyName", BCON_UTF8 (keyname), "KeyValue", BCON_UTF8 (value),"}");

    if (mongoc_collection_update (collection, MONGOC_UPDATE_UPSERT, query, update, NULL, &error)) result = NOPROBLEM_BIT;
    if (doc) bson_destroy (doc);
    if (query) bson_destroy (query);
    if (update) bson_destroy (update);
    return result;
}

FunctionResult mongoInsertDocument(char* buffer)
{ // comes from USER script, not the file system
	char* revisedBuffer = GetUserFileBuffer(); // use a filesystem buffer
	char* dot = strchr(ARGUMENT(1),'.');
	if (dot) *dot = 0;	 // terminate any suffix, not legal in mongo key
	strcpy(revisedBuffer,ARGUMENT(2)); // content to do
	FunctionResult result =  MongoUpsertDoc(true,ARGUMENT(1),revisedBuffer);
	if (dot) *dot = '.';	 // terminate any suffix, not legal in mongo key
	FreeUserCache();	// release back to file system
	return result;
}

//====  mongo C client calls ===========================================================================================

void MongoUserFilesClose()
{
	FunctionResult result = MongoClose(NULL);
	InitUserFiles(); // default back to normal filesystem
}

FILE* mongouserCreate(const char* name) // pretend user topic filename a file
{
	return (FILE*)name;
}

FILE* mongouserOpen(const char* name) // pretend user topic filename a file
{
	return (FILE*)name;
}

int mongouserClose(FILE*)
{
	return 0;
}

size_t mongouserRead(void* buffer,size_t size, size_t count, FILE* file)
{ // file buffer passed to us. Read everything, ignore size/count
	mongoBuffer = (char*) buffer; // will be a filebuffer
	*mongoBuffer = 0;
	char* dot = strchr((char*)file,'.');
	if (dot) *dot = 0;	 // terminate any suffix, not legal in mongo key
	FunctionResult result = mongoGetDocument((char*)file,mongoBuffer,(userCacheSize - MAX_USERNAME),false);
	if (dot) *dot ='.';	 
	return (result == NOPROBLEM_BIT) ? 1 : -1; // -1 is cannot find
}

size_t mongouserWrite(const void* buffer,size_t size, size_t count, FILE* file)
{// writes topic files, export files, server log files
	// data is already mongo safe, except for possible cr/nl 
	char* mongoBuffer = (char*) buffer;
	ProtectNL(mongoBuffer); // replace cr/nl
	char* dot = strchr((char*)file,'.');
	if (dot) *dot = 0;	 // terminate any suffix, not legal in mongo key
	FunctionResult result = MongoUpsertDoc(false,(char*)file, mongoBuffer);
	if (dot) *dot ='.';	 
	if (result != NOPROBLEM_BIT) return 0; // failed
	return size * count; // is len a match
}

void MonogoUserFilesInit() // start mongo as fileserver
{
	FunctionResult result = MongoInit(NULL); // files init
	if (result == NOPROBLEM_BIT)
	{
		// these are dynamically stored, so CS can be a DLL.
		userFileSystem.userCreate = mongouserCreate;
		userFileSystem.userOpen = mongouserOpen;
		userFileSystem.userClose = mongouserClose;
		userFileSystem.userRead = mongouserRead;
		userFileSystem.userWrite = mongouserWrite;
		filesystemOverride = MONGOFILES;
	}
	else 
	{
		ReportBug("Unable to open mongo fileserver");
		Log(SERVERLOG,"Unable to open mongo fileserver");
		printf("Unable to open mongo fileserver");
	}
}

void MongoSystemInit(char* params) // required
{
	if (!params) return;
	char arg1[MAX_WORD_SIZE];
	char arg2[MAX_WORD_SIZE];
	char arg3[MAX_WORD_SIZE];
	params = ReadCompiledWord(params,arg1);
	params = ReadCompiledWord(params,arg2);
	params = ReadCompiledWord(params,arg3);
	ARGUMENT(1) = arg1;
	ARGUMENT(2) = arg2;
	ARGUMENT(3) = arg3;
	MonogoUserFilesInit();
}

void MongoSystemRestart()
{
	MongoUserFilesClose();
}

void MongoSystemShutdown() // required
{
	char buffer[10];
	mongoShutdown = true;
	MongoClose(buffer); // close user one not closed
	MongoUserFilesClose();
	if (mongoInited) mongoc_cleanup();
}
#endif     // END OF DISCARDMONGO

