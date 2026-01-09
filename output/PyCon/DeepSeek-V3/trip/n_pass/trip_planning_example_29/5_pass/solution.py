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
    
    # Duration constraints - each stay must fit within the 10-day period
    for city in cities:
        duration = durations[city]
        problem.addConstraint(
            lambda arrival, dur=duration: arrival + dur <= 11,
            [f'arrival_{city}']
        )
    
    # Krakow wedding constraint - must be in Krakow on days 9-10
    # This means arrival_Krakow <= 9 and departure_Krakow >= 11
    # Since duration is 2 days, arrival must be exactly on day 9
    problem.addConstraint(
        lambda arr_k: arr_k == 9,
        ['arrival_Krakow']
    )
    
    # Total trip constraint: must start on day 1 and end on day 11
    # But allow for travel days between cities
    problem.addConstraint(
        lambda arr_f, arr_k, arr_d: 
            min(arr_f, arr_k, arr_d) == 1,
        ['arrival_Frankfurt', 'arrival_Krakow', 'arrival_Dubrovnik']
    )
    
    problem.addConstraint(
        lambda arr_f, arr_k, arr_d: 
            max(arr_f + 3, arr_k + 2, arr_d + 7) == 11,
        ['arrival_Frankfurt', 'arrival_Krakow', 'arrival_Dubrovnik']
    )
    
    # No overlapping stays constraint
    def no_overlap(arr_f, arr_k, arr_d):
        # Create stay intervals
        stays = [
            ('Frankfurt', arr_f, arr_f + 3),
            ('Krakow', arr_k, arr_k + 2),
            ('Dubrovnik', arr_d, arr_d + 7)
        ]
        
        # Check all pairs for overlap
        for i in range(3):
            for j in range(i + 1, 3):
                start1, end1 = stays[i][1], stays[i][2]
                start2, end2 = stays[j][1], stays[j][2]
                
                # Check if intervals overlap (excluding endpoints)
                if max(start1, start2) < min(end1, end2):
                    return False
        return True
    
    problem.addConstraint(no_overlap, [
        'arrival_Frankfurt', 'arrival_Krakow', 'arrival_Dubrovnik'
    ])
    
    # Flight connectivity constraints - more flexible approach
    def valid_flights(arr_f, arr_k, arr_d):
        # Create list of stays with city, arrival, and departure
        stays = [
            ('Frankfurt', arr_f, arr_f + 3),
            ('Krakow', arr_k, arr_k + 2),
            ('Dubrovnik', arr_d, arr_d + 7)
        ]
        
        # Sort by arrival time
        stays.sort(key=lambda x: x[1])
        
        # Check transitions between consecutive stays
        for i in range(len(stays) - 1):
            current_city, current_arr, current_dep = stays[i]
            next_city, next_arr, next_dep = stays[i + 1]
            
            # Allow travel days (next arrival can be after current departure)
            if next_arr < current_dep:
                return False
            
            # Check if flight exists between these cities
            valid_transitions = [
                ('Frankfurt', 'Krakow'),
                ('Krakow', 'Frankfurt'), 
                ('Dubrovnik', 'Frankfurt'),
                ('Frankfurt', 'Dubrovnik')  # Assuming round-trip flights exist
            ]
            
            if (current_city, next_city) not in valid_transitions:
                return False
        
        return True
    
    problem.addConstraint(valid_flights, [
        'arrival_Frankfurt', 'arrival_Krakow', 'arrival_Dubrovnik'
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
        departure = arrival + durations[city]
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