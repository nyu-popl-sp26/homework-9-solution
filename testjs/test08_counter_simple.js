const counterClass = (rep: {let x: Num}) => {
  inc: () => {rep.x = rep.x + 1;},
  get: () => rep.x
};

const newCounter = () => {
  const rep = { x: 0 };
  return counterClass(rep);
};

const counterClient =
  (c: {let inc: () => Undefined, let get: () => Num}) => {
    c.inc();
    c.inc();
    c.inc();
  };

const counter = newCounter();

counterClient(counter);
console.log(counter.get());
