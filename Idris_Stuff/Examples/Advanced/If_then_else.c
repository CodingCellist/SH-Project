
void main(void)
{
    __teamplay_branch_energy(b1, b2);
    if (/*condition*/)
    {
        // ...
        // some operations which happen to use less energy
        // ...
    }
    else
    {
        // ...
        // some operations which happen to use more energy
        // ...
    }

    __teamplay_assert(b1 == b2);
}

