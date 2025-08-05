from z3 import *
import json

def main():
    cities = ['Hamburg', 'Zurich', 'Helsinki', 'Bucharest', 'Split']
    required_days = {
        'Hamburg': 2,
        'Zurich': 3,
        'Helsinki': 2,
        'Bucharest': 2,
        'Split': 7
    }
    
    flight_list = [
        ('Zurich', 'Helsinki'),
        ('Hamburg', 'Bucharest'),
        ('Helsinki', 'Hamburg'),
        ('Zurich', 'Hamburg'),
        ('Zurich', 'Bucharest'),
        ('Zurich', 'Split'),
        ('Helsinki', 'Split'),
        ('Split', 'Hamburg')
    ]
    
    flight_set = {frozenset({c1, c2}) for (c1, c2) in flight_list}
    
    disallowed_pairs = set()
    for i in range(len(cities)):
        for j in range(i+1, len(cities)):
            c1 = cities[i]
            c2 = cities[j]
            pair = frozenset({c1, c2})
            if pair not in flight_set:
                disallowed_pairs.add((c1, c2))
    
    days = list(range(1, 13))
    s = Solver()
    
    In = {}
    for city in cities:
        In[city] = {}
        for d in days:
            In[city][d] = Bool(f"In_{city}_{d}")
    
    first_day = {}
    last_day = {}
    for city in cities:
        first_day[city] = Int(f'first_{city}')
        last_day[city] = Int(f'last_{city}')
        s.add(first_day[city] >= 1, first_day[city] <= 12)
        s.add(last_day[city] >= 1, last_day[city] <= 12)
        s.add(last_day[city] >= first_day[city])
        s.add(last_day[city] - first_day[city] + 1 == required_days[city])
        for d in days:
            s.add(Implies(And(d >= first_day[city], d <= last_day[city]), In[city][d]))
            s.add(Implies(In[city][d], And(d >= first_day[city], d <= last_day[city])))
    
    for d in days:
        s.add(Or([In[city][d] for city in cities]))
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                for k in range(j+1, len(cities)):
                    c1, c2, c3 = cities[i], cities[j], cities[k]
                    s.add(Not(And(In[c1][d], In[c2][d], In[c3][d])))
    
    for d in days:
        for (c1, c2) in disallowed_pairs:
            s.add(Not(And(In[c1][d], In[c2][d])))
    
    for d in range(1, 12):
        common_cities = []
        for city in cities:
            common_cities.append(And(In[city][d], In[city][d+1]))
        s.add(Or(common_cities))
    
    s.add(And(first_day['Split'] <= 4, last_day['Split'] >= 4))
    s.add(And(first_day['Split'] <= 10, last_day['Split'] >= 10))
    s.add(Or(
        And(first_day['Zurich'] <= 1, last_day['Zurich'] >= 1),
        And(first_day['Zurich'] <= 2, last_day['Zurich'] >= 2),
        And(first_day['Zurich'] <= 3, last_day['Zurich'] >= 3)
    ))
    
    if s.check() == sat:
        m = s.model()
        day_strings = []
        for d in days:
            cities_today = []
            for city in cities:
                if is_true(m.evaluate(In[city][d], model_completion=True)):
                    cities_today.append(city)
            cities_today_sorted = sorted(cities_today)
            if len(cities_today_sorted) == 1:
                city_str = cities_today_sorted[0]
            else:
                city_str = " and ".join(cities_today_sorted)
            day_strings.append(city_str)
        
        grouped_itinerary = []
        current_str = day_strings[0]
        start_day = 1
        end_day = 1
        for day_num in range(2, 13):
            idx = day_num - 1
            if day_strings[idx] == current_str:
                end_day = day_num
            else:
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                grouped_itinerary.append({'day_range': day_range, 'place': current_str})
                current_str = day_strings[idx]
                start_day = day_num
                end_day = day_num
        if start_day <= 12:
            if start_day == end_day:
                day_range = f"Day {start_day}"
            else:
                day_range = f"Day {start_day}-{end_day}"
            grouped_itinerary.append({'day_range': day_range, 'place': current_str})
        
        result = {'itinerary': grouped_itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()