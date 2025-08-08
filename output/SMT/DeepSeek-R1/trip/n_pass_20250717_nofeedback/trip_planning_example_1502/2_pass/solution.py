from z3 import *

def main():
    s = Solver()
    
    cities = ['Santorini', 'Vienna', 'Madrid', 'Seville', 'Valencia', 'Krakow', 'Frankfurt', 'Bucharest', 'Riga', 'Tallinn']
    
    # Define duration variables for each trip
    durations = [Int(f'duration_{i}') for i in range(10)]
    for i in range(10):
        s.add(durations[i] >= 2, durations[i] <= 5)
    
    # Sum of all durations must be 27
    s.add(Sum(durations) == 27)
    
    # Define city assignment variables for each trip
    trip_city = [Int(f'trip_city_{i}') for i in range(10)]
    for i in range(10):
        s.add(trip_city[i] >= 0, trip_city[i] < 10)
    
    # Ensure each city is assigned exactly once
    s.add(Distinct(trip_city))
    
    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        dur_vals = [m.evaluate(durations[i]).as_long() for i in range(10)]
        tc_vals = [m.evaluate(trip_city[i]).as_long() for i in range(10)]
        
        # Build the itinerary
        current_start = 1
        itinerary = []
        for i in range(10):
            d = dur_vals[i]
            end_day = current_start + d - 1
            city_index = tc_vals[i]
            city_name = cities[city_index]
            itinerary.append({
                'day_range': f'Day {current_start}-{end_day}',
                'place': city_name
            })
            current_start = end_day + 1
        
        # Verify the last day is 27
        if current_start - 1 == 27:
            print(f"Plan found: {{'itinerary': {itinerary}}}")
        else:
            print("Error: The plan does not end on day 27.")
    else:
        print("No valid plan found.")

if __name__ == '__main__':
    main()