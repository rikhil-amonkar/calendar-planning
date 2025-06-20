from z3 import *
import json

def main():
    Cities = ['Dubrovnik', 'Split', 'Milan', 'Porto', 'Krakow', 'Munich']
    required_days = {
        'Dubrovnik': 4,
        'Split': 3,
        'Milan': 3,
        'Porto': 4,
        'Krakow': 2,
        'Munich': 5
    }
    direct_flights = [
        ('Munich','Porto'), 
        ('Split','Milan'), 
        ('Milan','Porto'), 
        ('Munich','Krakow'), 
        ('Munich','Milan'), 
        ('Dubrovnik','Munich'), 
        ('Krakow','Split'), 
        ('Krakow','Milan'), 
        ('Munich','Split')
    ]
    allowed_pairs = set()
    for (a, b) in direct_flights:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    
    CitySort, city_consts = EnumSort('City', Cities)
    city_dict = {name: const for name, const in zip(Cities, city_consts)}
    City = CitySort
    
    morning_city = [Const(f'morning_{i}', City) for i in range(16)]
    evening_city = [Const(f'evening_{i}', City) for i in range(16)]
    
    s = Solver()
    
    for i in range(15):
        s.add(evening_city[i] == morning_city[i+1])
    
    for i in range(16):
        c1 = morning_city[i]
        c2 = evening_city[i]
        s.add(If(c1 != c2,
                 Or([And(c1 == city_dict[a], c2 == city_dict[b]) for (a, b) in allowed_pairs]),
                 True))
    
    wedding_days = [10, 11, 12]
    s.add(Or([Or(morning_city[i] == city_dict['Milan'], evening_city[i] == city_dict['Milan']) for i in wedding_days]))
    
    meeting_days = [7, 8]
    s.add(Or([Or(morning_city[i] == city_dict['Krakow'], evening_city[i] == city_dict['Krakow']) for i in meeting_days]))
    
    show_days = [3, 4, 5, 6, 7]
    s.add(Or([Or(morning_city[i] == city_dict['Munich'], evening_city[i] == city_dict['Munich']) for i in show_days]))
    
    for city in Cities:
        count_morning = Sum([If(morning_city[i] == city_dict[city], 1, 0) for i in range(16)])
        count_evening = Sum([If(evening_city[i] == city_dict[city], 1, 0) for i in range(16)])
        count_non_flight = Sum([If(And(morning_city[i] == city_dict[city], evening_city[i] == city_dict[city]), 1, 0) for i in range(16)])
        total = count_morning + count_evening - count_non_flight
        s.add(total == required_days[city])
    
    if s.check() == sat:
        model = s.model()
        morning_vals = []
        evening_vals = []
        for i in range(16):
            m_city = model.evaluate(morning_city[i])
            morning_vals.append(Cities[city_consts.index(m_city)])
            e_city = model.evaluate(evening_city[i])
            evening_vals.append(Cities[city_consts.index(e_city)])
        
        city_days = {city: set() for city in Cities}
        for i in range(16):
            day = i+1
            city_days[morning_vals[i]].add(day)
            city_days[evening_vals[i]].add(day)
        
        blocks = []
        for city in Cities:
            days = sorted(city_days[city])
            if not days:
                continue
            intervals = []
            start = days[0]
            end = days[0]
            for j in range(1, len(days)):
                if days[j] == end + 1:
                    end = days[j]
                else:
                    intervals.append((start, end, city))
                    start = days[j]
                    end = days[j]
            intervals.append((start, end, city))
            blocks.extend(intervals)
        
        flight_records = []
        for i in range(16):
            if morning_vals[i] != evening_vals[i]:
                day = i+1
                flight_records.append((day, morning_vals[i]))
                flight_records.append((day, evening_vals[i]))
        
        all_records = []
        for (start, end, city) in blocks:
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            all_records.append((start, 1, day_range, city))
        for (day, city) in flight_records:
            all_records.append((day, 0, f"Day {day}", city))
        
        all_records.sort(key=lambda x: (x[0], x[1]))
        itinerary_list = [{"day_range": dr, "place": city} for (_, _, dr, city) in all_records]
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()