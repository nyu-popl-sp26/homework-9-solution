/* Call-By-Name:
 *
 * With call-by-name, we can write a function that looks very
 * close to a custom statement.  For example, we define a
 *  'while' loop below.
 */

const while = function while(name cond: Bool): (name Undefined) => Undefined  {
    return (name body: Undefined) => cond ? (body, while(cond)(body)) : undefined;
  };

let i = 0;
while (i < 10) ({
  console.log(i);
  i = i + 1;
  undefined;
});

