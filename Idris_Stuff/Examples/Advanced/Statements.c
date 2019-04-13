void main(void)
{
    // ...
    // function definitions
    // ...
    
    __teamplay_worst_time(rd_time);
    void* val = readVal();

    __teamplay_worst_time(wr_time);
    __teamplay_worst_energy(wr_energy);
    int err = writeVal(val);

    __teamplay_assert((wr_time > rd_time) && (wr_energy <= 10));
}

