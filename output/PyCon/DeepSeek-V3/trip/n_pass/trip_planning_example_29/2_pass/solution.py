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
            lambda arrival, departure, dur=duration: departure - arrival == dur,
            [f'arrival_{city}', f'departure_{city}']
        )
    
    # Krakow wedding constraint (must be in Krakow on days 9-10)
    problem.addConstraint(
        lambda arr_k, dep_k: arr_k <= 9 and dep_k >= 10,
        ['arrival_Krakow', 'departure_Krakow']
    )
    
    # Total trip constraint: must start on day 1 and end on day 11
    problem.addConstraint(
        lambda arr_f, arr_k, arr_d, dep_f, dep_k, dep_d: 
            min(arr_f, arr_k, arr_d) == 1 and max(dep_f, dep_k, dep_d) == 11,
        ['arrival_Frankfurt', 'arrival_Krakow', 'arrival_Dubrovnik',
         'departure_Frankfurt', 'departure_Krakow', 'departure_Dubrovnik']
    )
    
    # No overlapping stays constraint
    def no_overlap(arr_f, dep_f, arr_k, dep_k, arr_d, dep_d):
        # Check all pairs of cities for overlap
        pairs = [
            (arr_f, dep_f, arr_k, dep_k),  # Frankfurt vs Krakow
            (arr_f, dep_f, arr_d, dep_d),  # Frankfurt vs Dubrovnik  
            (arr_k, dep_k, arr_d, dep_d)   # Krakow vs Dubrovnik
        ]
        
        for arr1, dep1, arr2, dep2 in pairs:
            # Two stays overlap if one starts before the other ends and ends after the other starts
            if not (dep1 <= arr2 or dep2 <= arr1):
                return False
        return True
    
    problem.addConstraint(no_overlap, [
        'arrival_Frankfurt', 'departure_Frankfurt',
        'arrival_Krakow', 'departure_Krakow',
        'arrival_Dubrovnik', 'departure_Dubrovnik'
    ])
    
    # Flight connectivity constraints
    def valid_flights(arr_f, dep_f, arr_k, dep_k, arr_d, dep_d):
        # Available flights: Frankfurt-Krakow and Dubrovnik-Frankfurt
        # This means we can only travel directly between these city pairs
        
        # Count valid transitions
        transitions = []
        
        # Frankfurt -> Krakow
        if dep_f == arr_k:
            transitions.append(('Frankfurt', 'Krakow'))
        
        # Krakow -> Frankfurt  
        if dep_k == arr_f:
            transitions.append(('Krakow', 'Frankfurt'))
        
        # Dubrovnik -> Frankfurt
        if dep_d == arr_f:
            transitions.append(('Dubrovnik', 'Frankfurt'))
        
        # Frankfurt -> Dubrovnik (NOT available)
        if dep_f == arr_d:
            return False
        
        # Krakow -> Dubrovnik (NOT available)  
        if dep_k == arr_d:
            return False
        
        # Dubrovnik -> Krakow (NOT available)
        if dep_d == arr_k:
            return False
        
        # We need exactly 2 transitions for visiting 3 cities
        return len(transitions) == 2
    
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