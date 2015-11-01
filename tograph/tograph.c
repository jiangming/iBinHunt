/*Ming Jiang   6-28*/

#include <sys/types.h>
#include <dirent.h>
#include <errno.h>
#include <string.h>



#define IR_DIR .
#define DB_SUFFIX ".db"
#define IR_PREFFIX "ir__"

#define MAX_LEN 256
#define COMMMAND_LEN 256

#define PREPROCESS_DIR "../static_analyze"
#define CALLINSTS_DIR "../static_analyze"

#define  DOT_PREFFIX  "cfg_"

int main(int argc, char** argv)
{
	char szCommand[COMMMAND_LEN] = {0};	
	char szDbPath[MAX_LEN] = {0};
	char szDbName[MAX_LEN] = {0};

	char* pDot = '\0';
	char* pSlash = '\0';
	int nRet = 0;
	
	strncpy(szDbPath, argv[1], MAX_LEN);
	pSlash = strrchr(szDbPath, '\/');
	if (pSlash)
		strcpy(szDbName, pSlash+1);
	else
		strcpy(szDbName, szDbPath);

	pDot = strrchr(szDbName, '.');
	if (pDot)
		*pDot = '\0';

    sprintf(szCommand, "mkdir ./result",szDbName);
	system(szCommand);

	sprintf(szCommand, "mkdir ./debug",szDbName);
	system(szCommand);

	sprintf(szCommand, "mkdir ./result/%s/",szDbName);
	system(szCommand);

	sprintf(szCommand, "mkdir ./debug/%s/",szDbName);
	system(szCommand);

	sprintf(szCommand, "mkdir ./debug/dot",szDbName);
	system(szCommand);

	sprintf(szCommand, "mkdir ./result/%s/dot",szDbName);
	system(szCommand);

	sprintf(szCommand, "%s/convert %s",  PREPROCESS_DIR, szDbPath);	
	system(szCommand);


	sprintf(szCommand, "%s/callinsts  %s%s.db", CALLINSTS_DIR, IR_PREFFIX, szDbName);	
	printf("%s\n", szCommand);
	system(szCommand);

	sprintf(szCommand, "mv ./debug/cfgprint.debug  ./result/%s/",szDbName);	
	system(szCommand);

	sprintf(szCommand, "mv ./debug/cgprint.debug  ./result/%s/",szDbName);	
	system(szCommand);

	sprintf(szCommand, "mv ./ir__%s.db  ./debug/%s/",szDbName, szDbName);	
	system(szCommand);

	sprintf(szCommand, "mv ./vineIR  ./debug/%s/",szDbName);	
	system(szCommand);

	sprintf(szCommand, "mv ./debug.txt  ./debug/%s/",szDbName);	
	system(szCommand);

    sprintf(szCommand, "mv ./debug/callinsts.debug  ./debug/%s/",szDbName);	
	system(szCommand);


	sprintf(szCommand, "mv ./debug/dot/*.*  ./result/%s/dot",szDbName);	
	system(szCommand);

}
