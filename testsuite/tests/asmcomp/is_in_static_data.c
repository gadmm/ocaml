#include "caml/address_class.h"

value is_in_static_data(value v) {
  return(Val_bool(caml_is_in_static_data((void *)v)));
}
