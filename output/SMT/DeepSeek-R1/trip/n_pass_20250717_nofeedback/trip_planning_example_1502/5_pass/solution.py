from z3 import *

def main():
    s = Solver()
    
    cities = ['Santorini', 'Vienna', 'Madrid', 'Seville', 'Valencia', 'Krakow', 'Frankfurt', 'Bucharest', 'Riga', 'Tallinn']
    num_cities = len(cities)
    days_total = 27
    days = range(days_total)  # 0-indexed: 0=day1, 26=day27
    
    # City for each day (0-indexed)
    city_day = [Int(f'city_day_{d}') for d in days]
    # Start and end day (0-indexed) for each city
    start_city = [Int(f'start_city_{c}') for c in range(num_cities)]
    end_city = [Int(f'end_city_{c}') for c in range(num_cities)]
    
    # Each day has a city index (0 to 9)
    for d in days:
        s.add(city_day[d] >= 0, city_day[d] < num_cities)
    
    # Constraints for each city
    for c in range(num_cities):
        # Start and end are within [0, days_total-1]
        s.add(start_city[c] >= 0, start_city[c] < days_total)
        s.add(end_city[c] >= 0, end_city[c] < days_total)
        
        # Duration constraint: 2-5 days
        s.add(end_city[c] - start_city[c] + 1 >= 2)
        s.add(end_city[c] - start_city[c] + 1 <= 5)
        
        # City appears in all days of its block
        for d in days:
            in_block = And(start_city[c] <= d, d <= end_city[c])
            s.add(Implies(in_block, city_day[d] == c))
            
            # City doesn't appear outside its block
            outside_block = Or(d < start_city[c], d > end_city[c])
            s.add(Implies(outside_block, city_day[d] != c))
    
    # Entire trip starts at day1 and ends at day27
    s.add(start_city[city_day[0]] == 0)
    s.add(end_city[city_day[days_total-1]] == days_total-1)
    
    # Solve and output
    if s.check() == sat:
        model = s.model()
        # Collect start/end days for each city
        trips = []
        for c in range(num_cities):
            start_val = model.evaluate(start_city[c]).as_long()
            end_val = model.evaluate(end_city[c]).as_long()
            trips.append({
                'city': cities[c],
                'start': start_val,
                'end': end_val
            })
        
        # Sort trips by start day
        trips.sort(key=lambda x: x['start'])
        
        # Build itinerary in chronological order
        itinerary = []
        for trip in trips:
            start_day = trip['start'] + 1  # Convert to 1-indexed
            end_day = trip['end'] + 1      # Convert to 1-indexed
            itinerary.append({
                'day_range': f'Day {start_day}-{end_day}',
                'place': trip['city']
            })
        
        print(f"Plan found: {{'itinerary': {itinerary}}}")
    else:
        print("No valid plan found.")

if __name__ == '__main__':
    main()