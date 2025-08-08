from z3 import *
import json

def main():
    city_names = {0: 'Mykonos', 1: 'Budapest', 2: 'Hamburg'}
    start_city = [Int('start_city_%d' % d) for d in range(9)]
    
    s = Solver()
    
    for i in range(9):
        s.add(Or(start_city[i] == 0, start_city[i] == 1, start_city[i] == 2))
    
    for i in range(8):
        s.add(
            If(
                start_city[i] != start_city[i+1],
                Or(
                    And(start_city[i] == 0, start_city[i+1] == 1),
                    And(start_city[i] == 1, start_city[i+1] == 0),
                    And(start_city[i] == 1, start_city[i+1] == 2),
                    And(start_city[i] == 2, start_city[i+1] == 1)
                ),
                True
            )
        )
    
    def in_city(day_index, city):
        if day_index < 8:
            return Or(
                start_city[day_index] == city,
                And(start_city[day_index] != city, start_city[day_index+1] == city)
            )
        else:
            return start_city[day_index] == city
    
    s.add(in_city(3, 0))
    s.add(in_city(8, 0))
    
    total_mykonos = Sum([If(in_city(i, 0), 1, 0) for i in range(9)])
    total_budapest = Sum([If(in_city(i, 1), 1, 0) for i in range(9)])
    total_hamburg = Sum([If(in_city(i, 2), 1, 0) for i in range(9)])
    
    s.add(total_mykonos == 6)
    s.add(total_budapest == 3)
    s.add(total_hamburg == 2)
    
    if s.check() == sat:
        m = s.model()
        start_vals = [m.evaluate(start_city[i]).as_long() for i in range(9)]
        
        days_in_city = {0: [], 1: [], 2: []}
        for c in [0, 1, 2]:
            for i in range(9):
                if start_vals[i] == c:
                    days_in_city[c].append(i+1)
                elif i < 8 and start_vals[i+1] == c and start_vals[i] != c:
                    days_in_city[c].append(i+1)
        
        stays = []
        for c, days in days_in_city.items():
            if not days:
                continue
            days.sort()
            start_interval = days[0]
            end_interval = days[0]
            for j in range(1, len(days)):
                if days[j] == end_interval + 1:
                    end_interval = days[j]
                else:
                    stays.append((start_interval, end_interval, c))
                    start_interval = days[j]
                    end_interval = days[j]
            stays.append((start_interval, end_interval, c))
        
        itinerary_list = []
        for start, end, c in stays:
            day_range = f"Day {start}-{end}" if start != end else f"Day {start}-{start}"
            itinerary_list.append({'day_range': day_range, 'place': city_names[c]})
        
        itinerary_list.sort(key=lambda x: int(x['day_range'].split('-')[0].split()[1]))
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()