import json
from z3 import *

def main():
    city_names = ["Naples", "Valencia", "Stuttgart", "Split", "Venice", "Amsterdam", "Nice", "Barcelona", "Porto"]
    city_index = {name: idx for idx, name in enumerate(city_names)}
    durations = [3, 5, 2, 5, 5, 4, 2, 2, 4]  # Corresponding to city_names order

    flights_str = "Venice and Nice, Naples and Amsterdam, Barcelona and Nice, Amsterdam and Nice, Stuttgart and Valencia, Stuttgart and Porto, Split and Stuttgart, Split and Naples, Valencia and Amsterdam, Barcelona and Porto, Valencia and Naples, Venice and Amsterdam, Barcelona and Naples, Barcelona and Valencia, Split and Amsterdam, Barcelona and Venice, Stuttgart and Amsterdam, Naples and Nice, Venice and Stuttgart, Split and Barcelona, Porto and Nice, Barcelona and Stuttgart, Venice and Naples, Porto and Amsterdam, Porto and Valencia, Stuttgart and Naples, Barcelona and Amsterdam"
    flights_list = [s.strip() for s in flights_str.split(',')]
    
    flight_set = set()
    for flight in flights_list:
        parts = flight.split(' and ')
        if len(parts) != 2:
            continue
        c1 = parts[0].strip()
        c2 = parts[1].strip()
        if c1 in city_index and c2 in city_index:
            i1 = city_index[c1]
            i2 = city_index[c2]
            flight_set.add((i1, i2))
            flight_set.add((i2, i1))
    
    flight_matrix = [[(i, j) in flight_set for j in range(len(city_names))] for i in range(len(city_names))]

    order = [Int(f'order_{i}') for i in range(9)]
    s_pos = [Int(f's_pos_{i}') for i in range(9)]
    city_start = [Int(f'city_start_{i}') for i in range(9)]

    solver = Solver()

    solver.add([And(order[i] >= 0, order[i] < 9) for i in range(9)])
    solver.add(Distinct(order))

    solver.add(s_pos[0] == 1)
    for i in range(1, 9):
        prev_duration = durations[order[i-1]]
        solver.add(s_pos[i] == s_pos[i-1] + prev_duration - 1)

    for c in range(9):
        solver.add(city_start[c] == Sum([If(order[j] == c, s_pos[j], 0) for j in range(9)]))

    solver.add(city_start[city_index["Naples"]] >= 16, city_start[city_index["Naples"]] <= 20)
    solver.add(city_start[city_index["Venice"]] >= 2, city_start[city_index["Venice"]] <= 10)
    solver.add(city_start[city_index["Nice"]] >= 22, city_start[city_index["Nice"]] <= 23)
    solver.add(city_start[city_index["Barcelona"]] >= 4, city_start[city_index["Barcelona"]] <= 6)

    flight_ok = Function('flight_ok', IntSort(), IntSort(), BoolSort())
    for i in range(9):
        for j in range(9):
            if flight_matrix[i][j]:
                solver.add(flight_ok(i, j))
            else:
                solver.add(Not(flight_ok(i, j)))
    
    for i in range(8):
        solver.add(flight_ok(order[i], order[i+1]))

    if solver.check() == sat:
        model = solver.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(9)]
        s_pos_val = [0] * 9
        s_pos_val[0] = 1
        for i in range(1, 9):
            prev_duration = durations[order_val[i-1]]
            s_pos_val[i] = s_pos_val[i-1] + prev_duration - 1

        city_start_val = [0] * 9
        for j in range(9):
            city_idx = order_val[j]
            city_start_val[city_idx] = s_pos_val[j]

        itinerary_list = []
        for day in range(1, 25):
            for c in range(9):
                start = city_start_val[c]
                end = start + durations[c] - 1
                if start <= day <= end:
                    itinerary_list.append({"day": day, "place": city_names[c]})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()