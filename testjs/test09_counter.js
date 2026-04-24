const counterClass = (rep: {let x: Num}) => {
  inc: () => { rep.x = rep.x + 1; },
  get: () => rep.x
};

const newCounter = () => {
  const rep = { x: 0 };
  return counterClass(rep);
};

const counterClient = (c: {let inc: () => Undefined}) => {
  c.inc();
  c.inc();
  c.inc();
};

const counter = newCounter();

counterClient(counter); // type error (needs subtyping)
console.log(counter.get());
