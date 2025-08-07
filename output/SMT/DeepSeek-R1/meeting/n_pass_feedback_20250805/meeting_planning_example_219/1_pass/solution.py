from z3 import *

def min_to_time(mins):
    total_minutes = 9 * 60 + mins
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    E = Bool('E')
    B = Bool('B')
    W = Bool('W')
    E_start = Real('E_start')
    E_end = Real('E_end')
    B_start = Real('B_start')
    B_end = Real('B_end')
    W_start = Real('W_start')
    W_end = Real('W_end')

    s = Solver()

    constraints = []

    # Meeting constraints
    constraints.append(Implies(E, And(E_start >= 165, E_end == E_start + 105, E_end <= 375)))
    constraints.append(Implies(B, And(B_start >= 465, B_end == B_start + 60, B_end <= 555)))
    constraints.append(Implies(W, And(W_start >= 495, W_end == W_start + 105, W_end <= 600)))

    # Travel constraints for combinations
    constraints.append(If(And(E, B, W),
        Or(
            And(B_start >= E_end + 14, W_start >= B_end + 7),
            And(W_start >= E_end + 16, B_start >= W_end + 7)
        ),
        True
    ))

    constraints.append(If(And(E, B, Not(W)),
        And(B_start >= E_end + 14, B_start >= 465),
        True
    ))

    constraints.append(If(And(E, W, Not(B)),
        And(W_start >= E_end + 16, W_start >= 495),
        True
    ))

    constraints.append(If(And(Not(E), B, W),
        Or(
            And(B_start >= 19, W_start >= B_end + 7),
            And(W_start >= 20, B_start >= W_end + 7)
        ),
        True
    ))

    s.add(constraints)

    options = [
        And(E, B, W),           # three meetings
        And(E, B, Not(W)),      # Emily and Barbara
        And(E, W, Not(B)),      # Emily and William
        And(Not(E), B, W),      # Barbara and William
        Or(E, B, W)             # at least one meeting
    ]

    model = None
    for opt in options:
        s.push()
        s.add(opt)
        if s.check() == sat:
            model = s.model()
            s.pop()
            break
        else:
            s.pop()

    itinerary = []
    if model is not None:
        if is_true(model[E]):
            e_start_val = model[E_start]
            if e_start_val.is_int():
                e_start_val = e_start_val.as_long()
            else:
                e_start_val = int(str(e_start_val))
            e_end_val = e_start_val + 105
            itinerary.append({
                "action": "meet",
                "person": "Emily",
                "start_time": min_to_time(e_start_val),
                "end_time": min_to_time(e_end_val)
            })
        if is_true(model[B]):
            b_start_val = model[B_start]
            if b_start_val.is_int():
                b_start_val = b_start_val.as_long()
            else:
                b_start_val = int(str(b_start_val))
            b_end_val = b_start_val + 60
            itinerary.append({
                "action": "meet",
                "person": "Barbara",
                "start_time": min_to_time(b_start_val),
                "end_time": min_to_time(b_end_val)
            })
        if is_true(model[W]):
            w_start_val = model[W_start]
            if w_start_val.is_int():
                w_start_val = w_start_val.as_long()
            else:
                w_start_val = int(str(w_start_val))
            w_end_val = w_start_val + 105
            itinerary.append({
                "action": "meet",
                "person": "William",
                "start_time": min_to_time(w_start_val),
                "end_time": min_to_time(w_end_val)
            })
    else:
        itinerary = []

    # Sort itinerary by start_time
    itinerary.sort(key=lambda x: x['start_time'])
    result = {"itinerary": itinerary}
    print("SOLUTION:")
    print(result)

if __name__ == "__main__":
    main()