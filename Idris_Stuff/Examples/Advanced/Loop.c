
void main(void) {
    int acc;
    int measured;
    __teamplay_loop_time(measured, 3, 100);
    for (int i = 0; i < 100; i++) {
        // some operations that take some time
        __teamplay_loop_time_acc(acc);
    }
    __teamplay_assert(acc <= measured);
}

