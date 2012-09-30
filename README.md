using namespace bag::placeholders;
using namespace bag::constants;

// f(x,y,z) = 1+x*y - z
auto f = _1 + _x * _y - _z;

// g = df/dx
auto g = D(f,_x); // _y
