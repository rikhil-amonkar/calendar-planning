import json

def main():
    # Define the order of cities based on constraints
    order = ['Dubrovnik', 'Munich', 'Krakow', 'Split', 'Milan', 'Porto']
    
    # Define cities' durations and constraints
    cities_info = {
        'Dubrovnik': {'duration': 4},
        'Munich': {'duration': 5, 'start_day': 4},
        'Krakow': {'duration': 2, 'start_day': 8},
        'Split': {'duration': 3, 'start_day': 9},
        'Milan': {'duration': 3, 'start_day': 11},
        'Porto': {'duration': 4, 'start_day': 13},
    }
    
    # Direct flights between cities
    direct_flights = {
        ('Munich', 'Porto'),
        ('Split', 'Milan'),
        ('Milan', 'Porto'),
        ('Munich', 'Krakow'),
        ('Munich', 'Milan'),
        ('Dubrovnik', 'Munich'),
        ('Krakow', 'Split'),
        ('Krakow', 'Milan'),
        ('Munich', 'Split'),
    }
    
    # Calculate itinerary
    itinerary_data = []
    current_start = 1
    
    for city in order:
        info = cities_info[city]
        # Check if start_day is constrained and matches current_start
        if 'start_day' in info:
            if current_start != info['start_day']:
                raise ValueError(f"Conflict for {city}: expected start_day {info['start_day']}, but current_start is {current_start}")
        start_day = current_start
        duration = info['duration']
        end_day = start_day + duration - 1
        itinerary_data.append( (city, start_day, end_day) )
        current_start = end_day  # Next city starts on the end day of this city
    
    # Check transitions between cities
    transitions = []
    for i in range(len(itinerary_data) - 1):
        prev_city = itinerary_data[i][0]
        next_city = itinerary_data[i+1][0]
        transitions.append( (prev_city, next_city) )
    
    for prev, curr in transitions:
        if (prev, curr) not in direct_flights:
            raise ValueError(f"No direct flight from {prev} to {curr}")
    
    # Generate JSON output
    result = {"itinerary": []}
    for city, start, end in itinerary_data:
        day_range = f"Day {start}-{end}"
        result['itinerary'].append( {"day_range": day_range, "place": city} )
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()