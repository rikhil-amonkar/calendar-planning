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
                if (c1, c2) not in flights and (c2, c1) not in flights:
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
        records = []  # List to hold all records
        
        # Step 1: Segment records for contiguous stays in each city.
        for city in cities:
            days_present = []
            for d in range(1, 13):
                if m.evaluate(In[d][city]) == True:
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
            
            for (s_start, s_end) in segments:
                if s_start == s_end:
                    day_range_str = f"Day {s_start}"
                else:
                    day_range_str = f"Day {s_start}-{s_end}"
                records.append({
                    'type': 'segment',
                    'start_day': s_start,
                    'day_range': day_range_str,
                    'place': city
                })
        
        # Step 2: Flight day records for days with two cities.
        flight_days = []
        for d in range(1, 13):
            count = 0
            for c in cities:
                if m.evaluate(In[d][c]) == True:
                    count += 1
            if count == 2:
                flight_days.append(d)
                
        for d in flight_days:
            cities_on_d = []
            for c in cities:
                if m.evaluate(In[d][c]) == True:
                    cities_on_d.append(c)
            cities_on_d.sort()
            for c in cities_on_d:
                records.append({
                    'type': 'flight_day',
                    'start_day': d,
                    'day_range': f"Day {d}",
                    'place': c
                })
        
        # Sort records by start_day, then by type (segment first, then flight_day), then by place.
        def get_sort_key(rec):
            # For segment records, we have the start_day. For flight_day, it's the day itself.
            start = rec['start_day']
            # Type: segment -> 0, flight_day -> 1
            type_val = 0 if rec['type'] == 'segment' else 1
            place = rec['place']
            return (start, type_val, place)
        
        records_sorted = sorted(records, key=get_sort_key)
        itinerary = [{'day_range': rec['day_range'], 'place': rec['place']} for rec in records_sorted]
        
        # Output the result as JSON
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()