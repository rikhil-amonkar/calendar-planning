from z3 import *
import json

def main():
    # Cities encoding
    M, S, St = 0, 1, 2
    n_days = 15
    s = Solver()

    # Night stay variables for each day
    night = [Int('night_%d' % (i+1)) for i in range(n_days)]
    for i in range(n_days):
        s.add(Or(night[i] == M, night[i] == S, night[i] == St))

    # Transition constraints
    for i in range(1, n_days):
        s.add(If(night[i] != night[i-1],
                 Or(And(night[i-1] == M, night[i] == S),
                    And(night[i-1] == S, night[i] == M),
                    And(night[i-1] == M, night[i] == St),
                    And(night[i-1] == St, night[i] == M)),
                 True))

    # Presence variables
    in_M = [Bool('in_M_%d' % (i+1)) for i in range(n_days)]
    in_S = [Bool('in_S_%d' % (i+1)) for i in range(n_days)]
    in_St = [Bool('in_St_%d' % (i+1)) for i in range(n_days)]

    # Day 1 constraints
    s.add(in_M[0] == (night[0] == M))
    s.add(in_S[0] == (night[0] == S))
    s.add(in_St[0] == (night[0] == St))

    # Remaining days
    for i in range(1, n_days):
        s.add(in_M[i] == If(night[i] == night[i-1], night[i] == M, Or(night[i] == M, night[i-1] == M)))
        s.add(in_S[i] == If(night[i] == night[i-1], night[i] == S, Or(night[i] == S, night[i-1] == S)))
        s.add(in_St[i] == If(night[i] == night[i-1], night[i] == St, Or(night[i] == St, night[i-1] == St)))

    # Total days constraints
    total_M = Sum([If(in_M[i], 1, 0) for i in range(n_days)])
    total_S = Sum([If(in_S[i], 1, 0) for i in range(n_days)])
    total_St = Sum([If(in_St[i], 1, 0) for i in range(n_days)])
    s.add(total_M == 4, total_S == 7, total_St == 6)

    # Stuttgart constraint between days 1-6
    s.add(Or([in_St[i] for i in range(6)]))

    if s.check() == sat:
        m = s.model()
        night_values = [m.evaluate(night[i]).as_long() for i in range(n_days)]
        city_names = {M: "Manchester", S: "Seville", St: "Stuttgart"}
        
        itinerary = []
        start_day = 1
        current_city = night_values[0]
        
        for day in range(1, n_days):
            if night_values[day] != current_city:
                itinerary.append({
                    "day_range": f"Day {start_day}-{day}",
                    "place": city_names[current_city]
                })
                start_day = day + 1
                current_city = night_values[day]
                
        itinerary.append({
            "day_range": f"Day {start_day}-{n_days}",
            "place": city_names[current_city]
        })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()