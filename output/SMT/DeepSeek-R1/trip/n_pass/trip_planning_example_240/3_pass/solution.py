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
    
    # Create a 2D array of Bool variables: In[day][city]
    In = {}
    for d in range(1, 13):
        In[d] = {}
        for c in cities:
            In[d][c] = Bool(f"In_day{d}_{c}")
    
    s = Solver()
    
    # Constraint: Each day has either 1 or 2 cities.
    for d in range(1, 13):
        total = Sum([If(In[d][c], 1, 0) for c in cities])
        s.add(Or(total == 1, total == 2))
    
    # Constraint: If two cities are present on the same day, they must be connected by a direct flight.
    for d in range(1, 13):
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                c1 = cities[i]
                c2 = cities[j]
                pair = frozenset([c1, c2])
                if pair not in allowed_pairs_sym:
                    s.add(Not(And(In[d][c1], In[d][c2])))
    
    # Fixed constraints for Berlin: must be present on day 6 and 8.
    s.add(In[6]['Berlin'] == True)
    s.add(In[8]['Berlin'] == True)
    
    # Fixed constraints for Tallinn: must be present on days 8 to 12.
    for d in [8, 9, 10, 11, 12]:
        s.add(In[d]['Tallinn'] == True)
    
    # Total days per city
    s.add(Sum([If(In[d]['Prague'], 1, 0) for d in range(1,13)]) == 2)
    s.add(Sum([If(In[d]['Berlin'], 1, 0) for d in range(1,13)]) == 3)
    s.add(Sum([If(In[d]['Tallinn'], 1, 0) for d in range(1,13)]) == 5)
    s.add(Sum([If(In[d]['Stockholm'], 1, 0) for d in range(1,13)]) == 5)
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        # Create a list to hold all records
        records = []
        
        # For each city, find contiguous blocks of days
        for city in cities:
            days_present = []
            for d in range(1, 13):
                if is_true(m.evaluate(In[d][city])):
                    days_present.append(d)
            if not days_present:
                continue
            days_present.sort()
            segments = []
            start = days_present[0]
            end = days_present[0]
            for i in range(1, len(days_present)):
                if days_present[i] == end + 1:
                    end = days_present[i]
                else:
                    segments.append((start, end))
                    start = days_present[i]
                    end = days_present[i]
            segments.append((start, end))
            
            for seg in segments:
                start_day, end_day = seg
                if start_day == end_day:
                    day_range_str = f"Day {start_day}"
                else:
                    day_range_str = f"Day {start_day}-{end_day}"
                records.append({
                    'day_range': day_range_str,
                    'place': city,
                    'start_day': start_day
                })
        
        # Sort records by the start_day of the segment
        records_sorted = sorted(records, key=lambda x: x['start_day'])
        itinerary_list = [{'day_range': rec['day_range'], 'place': rec['place']} for rec in records_sorted]
        
        # Output the result as JSON
        result = {'itinerary': itinerary_list}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()