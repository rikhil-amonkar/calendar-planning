from z3 import *
import json

def main():
    n = 8
    city_names = {
        0: "Reykjavik",
        1: "Riga",
        2: "Oslo",
        3: "Lyon",
        4: "Dubrovnik",
        5: "Madrid",
        6: "Warsaw",
        7: "London"
    }
    req = [4, 2, 3, 5, 2, 2, 4, 3]  # corresponding to the cities in order 0 to 7

    flights_list = [
        (6, 0), (2, 5), (6, 1), (3, 7), (5, 7), (6, 7), (0, 5), (6, 2),
        (2, 4), (2, 0), (1, 2), (2, 3), (2, 7), (7, 0), (6, 5), (5, 3), (4, 5)
    ]
    directed_flights = []
    for a, b in flights_list:
        directed_flights.append((a, b))
        directed_flights.append((b, a))

    route = [Int('route_%d' % i) for i in range(n)]
    start_pos = [Int('start_pos_%d' % i) for i in range(n)]

    s = Solver()

    for i in range(n):
        s.add(route[i] >= 0, route[i] < n)
    s.add(Distinct(route))

    s.add(start_pos[0] == 1)

    req_array = Array('req_array', IntSort(), IntSort())
    for i in range(n):
        req_array = Store(req_array, i, req[i])

    for i in range(1, n):
        prev_req = Select(req_array, route[i - 1])
        s.add(start_pos[i] == start_pos[i - 1] + prev_req - 1)

    last_req = Select(req_array, route[n - 1])
    s.add(start_pos[n - 1] + last_req - 1 == 18)

    for i in range(n - 1):
        conds = []
        for a, b in directed_flights:
            conds.append(And(route[i] == a, route[i + 1] == b))
        s.add(Or(conds))

    def get_start_day(c):
        cases = [route[i] == c for i in range(n)]
        return If(cases[0], start_pos[0],
               If(cases[1], start_pos[1],
               If(cases[2], start_pos[2],
               If(cases[3], start_pos[3],
               If(cases[4], start_pos[4],
               If(cases[5], start_pos[5],
               If(cases[6], start_pos[6],
               start_pos[7]))))))

    s_riga = get_start_day(1)
    s_dubrovnik = get_start_day(4)
    s.add(Or(
        And(s_riga <= 4, 4 <= s_riga + 1),
        And(s_riga <= 5, 5 <= s_riga + 1)
    ))
    s.add(Or(
        And(s_dubrovnik <= 7, 7 <= s_dubrovnik + 1),
        And(s_dubrovnik <= 8, 8 <= s_dubrovnik + 1)
    ))

    if s.check() == sat:
        m = s.model()
        route_val = [m[route[i]].as_long() for i in range(n)]
        start_pos_val = [m[start_pos[i]].as_long() for i in range(n)]

        itinerary = []
        for i in range(n):
            city_index = route_val[i]
            start_day = start_pos_val[i]
            duration = req[city_index]
            end_day = start_day + duration - 1
            city_name = city_names[city_index]
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_name
            })
            if i < n - 1:
                itinerary.append({
                    "day_range": f"Day {end_day}",
                    "place": city_name
                })
                next_city_index = route_val[i + 1]
                next_city_name = city_names[next_city_index]
                itinerary.append({
                    "day_range": f"Day {end_day}",
                    "place": next_city_name
                })
                itinerary.append({
                    "day_range": f"Day {end_day}-{start_pos_val[i + 1] + req[next_city_index] - 1}",
                    "place": next_city_name
                })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()