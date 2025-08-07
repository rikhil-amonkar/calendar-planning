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

    s = Solver()

    # Define the order of cities (permutation)
    order = [Int(f'order_{i}') for i in range(9)]
    for i in range(9):
        s.add(order[i] >= 0, order[i] < 9)
    s.add(Distinct(order))

    # Define start positions for each city in the sequence
    s_pos = [Int(f's_pos_{i}') for i in range(9)]
    s.add(s_pos[0] == 1)

    # Constraints for s_pos: each subsequent city starts on the last day of the previous city
    for i in range(1, 9):
        prev_city = order[i-1]
        prev_duration = durations[prev_city]  # Using Python list for durations in constraints
        s.add(s_pos[i] == s_pos[i-1] + prev_duration - 1)

    # Define start day for each city
    city_start = [Int(f'city_start_{c}') for c in range(9)]
    for c in range(9):
        s.add(city_start[c] == Sum([If(order[j] == c, s_pos[j], 0) for j in range(9)]))

    # Constraints for specific cities
    s.add(city_start[city_index["Naples"]] >= 16, city_start[city_index["Naples"]] <= 20)
    s.add(city_start[city_index["Venice"]] >= 2, city_start[city_index["Venice"]] <= 10)
    s.add(city_start[city_index["Nice"]] >= 22, city_start[city_index["Nice"]] <= 23)
    s.add(city_start[city_index["Barcelona"]] >= 4, city_start[city_index["Barcelona"]] <= 6)

    # Flight constraints: consecutive cities must be connected by a direct flight
    for i in range(8):
        city1 = order[i]
        city2 = order[i+1]
        s.add(Or([And(city1 == idx1, city2 == idx2) for (idx1, idx2) in flight_set if flight_matrix[idx1][idx2]]))

    # Ensure the trip ends on day 24
    last_city = order[8]
    s.add(s_pos[8] + durations[last_city] - 1 == 24)

    if s.check() == sat:
        model = s.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(9)]
        s_pos_val = [model.evaluate(s_pos[i]).as_long() for i in range(9)]
        city_start_val = [model.evaluate(city_start[c]).as_long() for c in range(9)]

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