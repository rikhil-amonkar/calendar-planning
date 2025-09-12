from z3 import *
import json

def main():
    s = Solver()
    
    cities = [0, 1, 2, 3, 4, 5]
    city_names = {
        0: 'Dubrovnik',
        1: 'Split',
        2: 'Milan',
        3: 'Porto',
        4: 'Krakow',
        5: 'Munich'
    }
    durations = [4, 3, 3, 4, 2, 5]
    allowed_flights = [(5, 3), (1, 2), (2, 3), (5, 4), (5, 2), (0, 5), (4, 1), (4, 2), (5, 1)]
    
    order = [Int('o%d' % i) for i in range(6)]
    for i in range(6):
        s.add(order[i] >= 0, order[i] <= 5)
    s.add(Distinct(order))
    
    def dur(c):
        return If(c == 0, 4,
               If(c == 1, 3,
               If(c == 2, 3,
               If(c == 3, 4,
               If(c == 4, 2, 5)))))
    
    start_pos = [1]
    for i in range(1, 6):
        prev_start = start_pos[i-1]
        prev_dur = dur(order[i-1])
        start_pos.append(prev_start + prev_dur - 1)
    
    s.add(start_pos[5] + dur(order[5]) - 1 == 16)
    
    start_i = [None] * 6
    for city in cities:
        start_i[city] = If(order[0] == city, start_pos[0],
                        If(order[1] == city, start_pos[1],
                        If(order[2] == city, start_pos[2],
                        If(order[3] == city, start_pos[3],
                        If(order[4] == city, start_pos[4],
                        start_pos[5])))))
    
    s.add(start_i[5] <= 4)
    s.add(start_i[5] + dur(5) - 1 >= 8)
    s.add(start_i[2] <= 11)
    s.add(start_i[2] + dur(2) - 1 >= 13)
    s.add(start_i[4] <= 8)
    s.add(start_i[4] + dur(4) - 1 >= 9)
    
    for i in range(5):
        city_i = order[i]
        city_j = order[i+1]
        constraints = []
        for (a, b) in allowed_flights:
            constraints.append(And(city_i == a, city_j == b))
            constraints.append(And(city_i == b, city_j == a))
        s.add(Or(constraints))
    
    if s.check() == sat:
        m = s.model()
        order_val = [m.evaluate(order[i]).as_long() for i in range(6)]
        start_days = [m.evaluate(start_i[city]).as_long() for city in cities]
        
        stays = []
        for i in range(6):
            city_index = order_val[i]
            start = start_days[city_index]
            duration_val = durations[city_index]
            end = start + duration_val - 1
            stays.append((start, end, city_names[city_index]))
        
        stays.sort(key=lambda x: x[0])
        itinerary = []
        for stay in stays:
            start, end, city = stay
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()