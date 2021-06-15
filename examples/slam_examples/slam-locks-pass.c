/*
* Rules:
*   1) The spin lock may only be acquired if it is not currently held
*   2) The spin lock may only be released if it is currently held
*
* This example passes the rules.
*/

struct request
{
    int                 Status;
    struct request*     Next;
    struct ir_protocol* irp;
};

struct device_ext
{
    struct request* WLHV;
};

struct IO_STATUS_BLOCK
{
    int Status;
    int Info;
};

struct ir_protocol
{
    struct IO_STATUS_BLOCK IoS;
};

#define SUCCESS 0 
#define FAIL    1

extern void KeAcquireSpinLock();
extern void KeReleaseSpinLock();
extern int nPacketsOld;
extern int nPackets;
extern struct request* req;
extern struct device_ext* devExt;
extern struct ir_protocol* irp;
extern void SmartDevFreeBlock(struct request*);
extern void IoCompleteRequest(struct ir_protocol*);

void request()
{
    do
    {
        //Acquires lock every time
        KeAcquireSpinLock();

        nPacketsOld = nPackets;
        req = devExt->WLHV;
        if(req && req->Status)
        {
            devExt->WLHV = req->Next;

            irp = req->irp;
            if(req->Status > 0)
            {
                irp->IoS.Status = SUCCESS;
                irp->IoS.Info   = req->Status;
            }
            else
            {
                irp->IoS.Status = FAIL;
                irp->IoS.Info   = req->Status;
            }
            SmartDevFreeBlock(req);
            IoCompleteRequest(irp);
            nPackets++;
        }

        //Releases lock every time
        KeReleaseSpinLock();
    } while(nPackets!=nPacketsOld);
}
