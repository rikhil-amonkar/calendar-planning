from z3 import *

def main():
    cities = ['Prague', 'Berlin', 'Tallinn', 'Stockholm']
    flights = { 
        ('Berlin', 'Tallinn'), 
        ('Prague', 'Tallinn'), 
        ('Stockholm', 'Tallinn'), 
        ('Prague', 'Stockholm'), 
        ('Stockholm', 'Berlin')
    }
    allowed_pairs_sym = {frozenset(pair) for pair in flights}
    
    In = {}
    for d in range(1, 13):
        In[d] = {}
        for c in cities:
            In[d][c] = Bool(f"In_day{d}_{c}")
    
    s = Solver()
    
    for d in range(1, 13):
        total = Sum([If(In[d][c], 1, 0) for c in cities])
        s.add(Or(total == 1, total == 2))
    
    for d in range(1, 13):
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                pair = frozenset([c1, c2])
                if pair not in allowed_pairs_sym:
                    s.add(Not(And(In[d][c1], In[d][c2])))
    
    s.add(In[6]['Berlin'] == True)
    s.add(In[8]['Berlin'] == True)
    
    for d in [8, 9, 10, 11, 12]:
        s.add(In[d]['Tallinn'] == True)
    
    s.add(Sum([If(In[d]['Prague'], 1, 0) for d in range(1,13)]) == 2)
    s.add(Sum([If(In[d]['Berlin'], 1, 0) for d in range(1,13)]) == 3)
    s.add(Sum([If(In[d]['Tallinn'], 1, 0) for d in range(1,13)]) == 5)
    s.add(Sum([If(In[d]['Stockholm'], 1, 0) for d in range(1,13)]) == 5)
    
    if s.check() == sat:
        m = s.model()
        records = []
        
        day_city_count = {}
        for d in range(1, 13):
            count = 0
            for city in cities:
                if is_true(m.evaluate(In[d][city])):
                    count += 1
            day_city_count[d] = count
        
        for city in cities:
            sole_days = []
            flight_days = []
            for d in range(1, 13):
                if is_true(m.evaluate(In[d][city])):
                    if day_city_count[d] == 1:
                        sole_days.append(d)
                    else:
                        flight_days.append(d)
            
            sole_days.sort()
            segments = []
            if sole_days:
                start = sole_days[0]
                end = sole_days[0]
                for i in range(1, len(sole_days)):
                    if sole_days[i] == end + 1:
                        end = sole_days[i]
                    else:
                        segments.append((start, end))
                        start = sole_days[i]
                        end = sole_days[i]
                segments.append((start, end))
            
            for seg in segments:
                start, end = seg
                if start == end:
                    day_range = f"Day {start}"
                else:
                    day_range = f"Day {start}-{end}"
                records.append({
                    'day_range': day_range,
                    'place': city,
                    'start_day': start
                })
            
            for d in flight_days:
                records.append({
                    'day_range': f"Day {d}",
                    'place': city,
                    'start_day': d
                })
        
        records_sorted = sorted(records, key=lambda x: x['start_day'])
        itinerary_list = [{'day_range': rec['day_range'], 'place': rec['place']} for rec in records_sorted]
        
        result = {'itinerary': itinerary_list}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()