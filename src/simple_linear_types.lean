import type
import context

namespace simple_linear_types

inductive expr : Type
| var  : nat →         expr
| nat  : nat →         expr
| plus : expr → expr → expr
| bool : bool →        expr
| and  : expr → expr → expr


end simple_linear_types
