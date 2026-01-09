import json
from constraint import Problem

def solve_itinerary():
    # Define the problem
    problem = Problem()
    
    # Cities and their required stay durations
    cities = ['Frankfurt', 'Krakow', 'Dubrovnik']
    durations = {'Frankfurt': 3, 'Krakow': 2, 'Dubrovnik': 7}
    
    # Define arrival days for each city (1-10)
    for city in cities:
        problem.addVariable(f'arrival_{city}', range(1, 11))
    
    # Calculate departure days based on arrival and duration
    for city in cities:
        problem.addVariable(f'departure_{city}', range(1, 12))
    
    # Duration constraints
    for city in cities:
        duration = durations[city]
        problem.addConstraint(
            lambda arrival, departure, dur=duration: departure == arrival + dur,
            [f'arrival_{city}', f'departure_{city}']
        )
    
    # Krakow wedding constraint (must be in Krakow on days 9-10)
    # This means arrival <= 9 and departure >= 11 (since departure is exclusive)
    problem.addConstraint(
        lambda arr_k, dep_k: arr_k <= 9 and dep_k >= 11,
        ['arrival_Krakow', 'departure_Krakow']
    )
    
    # Total trip constraint: must start on day 1 and end on day 11
    problem.addConstraint(
        lambda arr_f, arr_k, arr_d, dep_f, dep_k, dep_d: 
            min(arr_f, arr_k, arr_d) == 1 and max(dep_f, dep_k, dep_d) == 11,
        ['arrival_Frankfurt', 'arrival_Krakow', 'arrival_Dubrovnik',
         'departure_Frankfurt', 'departure_Krakow', 'departure_Dubrovnik']
    )
    
    # No overlapping stays constraint - simplified approach
    def no_overlap(arr1, dep1, arr2, dep2, arr3, dep3):
        # Check all pairs of cities for overlap
        pairs = [
            (arr1, dep1, arr2, dep2),
            (arr1, dep1, arr3, dep3),  
            (arr2, dep2, arr3, dep3)
        ]
        
        for a1, d1, a2, d2 in pairs:
            # Two stays overlap if they are not completely separate
            if not (d1 <= a2 or d2 <= a1):
                return False
        return True
    
    problem.addConstraint(no_overlap, [
        'arrival_Frankfurt', 'departure_Frankfurt',
        'arrival_Krakow', 'departure_Krakow',
        'arrival_Dubrovnik', 'departure_Dubrovnik'
    ])
    
    # Flight connectivity constraints - relaxed approach
    def valid_flights(arr_f, dep_f, arr_k, dep_k, arr_d, dep_d):
        # Available flights: Frankfurt-Krakow and Dubrovnik-Frankfurt
        
        # Get the order of cities by arrival time
        arrivals = [
            ('Frankfurt', arr_f),
            ('Krakow', arr_k), 
            ('Dubrovnik', arr_d)
        ]
        arrivals.sort(key=lambda x: x[1])
        
        # Check transitions between consecutive cities in the itinerary
        valid_transitions = 0
        for i in range(len(arrivals) - 1):
            current_city, current_dep = arrivals[i][0], None
            next_city, next_arr = arrivals[i+1][0], arrivals[i+1][1]
            
            # Get departure for current city
            if current_city == 'Frankfurt':
                current_dep = dep_f
            elif current_city == 'Krakow':
                current_dep = dep_k
            else:  # Dubrovnik
                current_dep = dep_d
            
            # Check if this transition is valid
            if current_dep == next_arr:
                if (current_city == 'Frankfurt' and next_city == 'Krakow') or \
                   (current_city == 'Dubrovnik' and next_city == 'Frankfurt') or \
                   (current_city == 'Krakow' and next_city == 'Frankfurt'):
                    valid_transitions += 1
                else:
                    return False
        
        # We need exactly 2 valid transitions for visiting 3 cities
        return valid_transitions == 2
    
    problem.addConstraint(valid_flights, [
        'arrival_Frankfurt', 'departure_Frankfurt',
        'arrival_Krakow', 'departure_Krakow',
        'arrival_Dubrovnik', 'departure_Dubrovnik'
    ])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Build the itinerary in chronological order
    stays = []
    for city in cities:
        arrival = solution[f'arrival_{city}']
        departure = solution[f'departure_{city}']
        stays.append({
            'city': city,
            'arrival': arrival,
            'departure': departure
        })
    
    # Sort by arrival day
    stays.sort(key=lambda x: x['arrival'])
    
    # Build final itinerary
    itinerary = []
    for stay in stays:
        arrival = stay['arrival']
        departure = stay['departure']
        
        if departure - arrival == 1:
            day_range = f"Day {arrival}"
        else:
            day_range = f"Day {arrival}-{departure-1}"
        
        itinerary.append({
            "day_range": day_range,
            "place": stay['city']
        })
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))