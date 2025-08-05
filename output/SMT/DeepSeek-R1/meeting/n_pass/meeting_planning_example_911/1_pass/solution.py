from z3 import *
import json

def main():
    events = [-1] + list(range(10))
    meet = {}
    meet[-1] = True
    for i in range(10):
        meet[i] = Bool(f"meet_{i}")

    start = {}
    end = {}
    start[-1] = 540
    end[-1] = 540
    for i in range(10):
        start[i] = Real(f"start_{i}")
        end[i] = Real(f"end_{i}")

    T0 = [20, 11, 22, 6, 16, 16, 21, 20, 19, 21]
    T = [
        [0, 22, 6, 18, 18, 7, 9, 17, 7, 8],
        [23, 0, 25, 7, 7, 20, 16, 11, 22, 26],
        [5, 25, 0, 21, 21, 10, 12, 20, 10, 5],
        [19, 7, 20, 0, 10, 15, 17, 15, 19, 21],
        [17, 9, 19, 10, 0, 17, 9, 7, 21, 22],
        [8, 17, 9, 13, 14, 0, 11, 17, 7, 9],
        [11, 18, 14, 16, 11, 12, 0, 10, 16, 17],
        [18, 12, 20, 15, 7, 18, 11, 0, 22, 23],
        [10, 22, 11, 18, 20, 9, 18, 24, 0, 9],
        [7, 23, 4, 19, 21, 8, 15, 22, 9, 0]
    ]
    min_durations = [15, 75, 105, 75, 30, 90, 120, 120, 60, 45]
    availability = [
        (1050, 1230),
        (1020, 1155),
        (855, 960),
        (615, 735),
        (840, 1170),
        (495, 765),
        (675, 795),
        (900, 1095),
        (690, 1260),
        (795, 915)
    ]
    names = ["Steven", "Sarah", "Brian", "Stephanie", "Melissa", "Nancy", "David", "James", "Elizabeth", "Robert"]

    def travel_time(i, j):
        if i == -1 and j >= 0:
            return T0[j]
        elif i >= 0 and j >= 0:
            return T[i][j]
        else:
            return 0

    s = Solver()

    s.add(Implies(meet[2], And(start[2] == 855, end[2] == 960)))
    s.add(Implies(meet[6], And(start[6] == 675, end[6] == 795)))

    for i in range(10):
        if i not in [2, 6]:
            s.add(Implies(meet[i], end[i] == start[i] + min_durations[i]))

    for i in range(10):
        avail_start, avail_end = availability[i]
        s.add(Implies(meet[i], start[i] >= avail_start))
        s.add(Implies(meet[i], end[i] <= avail_end))

    before = {}
    for i in events:
        for j in events:
            if i != j:
                before[(i, j)] = Bool(f"before_{i}_{j}")

    for i in events:
        for j in events:
            if i == j:
                continue
            if i == -1 and j != -1:
                s.add(Implies(meet[j], before[(-1, j)]))
                s.add(Implies(meet[j], Not(before[(j, -1)])))
                s.add(Implies(meet[j], end[-1] + travel_time(-1, j) <= start[j]))
            elif j == -1:
                continue
            else:
                s.add(Implies(And(meet[i], meet[j]), Or(before[(i, j)], before[(j, i)])))
                s.add(Implies(And(meet[i], meet[j]), before[(i, j)] == Not(before[(j, i)])))
                s.add(Implies(And(meet[i], meet[j], before[(i, j)]), end[i] + travel_time(i, j) <= start[j]))
                s.add(Implies(And(meet[i], meet[j], before[(j, i)]), end[j] + travel_time(j, i) <= start[i]))

    opt = Optimize()
    opt.add(s.assertions())
    objective = Sum([If(meet[i], 1, 0) for i in range(10)])
    opt.maximize(objective)
    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for i in range(10):
            if is_true(model.eval(meet[i])):
                start_val = model.eval(start[i])
                end_val = model.eval(end[i])
                if is_rational_value(start_val):
                    start_minutes = start_val.numerator_as_long() // start_val.denominator_as_long()
                elif is_algebraic_value(start_val):
                    start_minutes = start_val.approx(10).as_long()
                else:
                    start_minutes = int(str(start_val))
                if is_rational_value(end_val):
                    end_minutes = end_val.numerator_as_long() // end_val.denominator_as_long()
                elif is_algebraic_value(end_val):
                    end_minutes = end_val.approx(10).as_long()
                else:
                    end_minutes = int(str(end_val))
                start_hour = start_minutes // 60
                start_minute = start_minutes % 60
                end_hour = end_minutes // 60
                end_minute = end_minutes % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                scheduled_meetings.append({
                    "action": "meet",
                    "person": names[i],
                    "start_time": start_str,
                    "end_time": end_str
                })
        scheduled_meetings.sort(key=lambda x: (x['start_time'], x['end_time']))
        result = {"itinerary": scheduled_meetings}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()