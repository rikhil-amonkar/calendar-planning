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
    
    # Duration constraints
    for city in cities:
        duration = durations[city]
        problem.addConstraint(
            lambda arrival, dur=duration: arrival + dur <= 11,
            [f'arrival_{city}']
        )
    
    # Krakow wedding constraint (must be in Krakow on days 9-10)
    # This means arrival <= 9 and departure >= 11
    problem.addConstraint(
        lambda arr_k: arr_k <= 9 and arr_k + 2 >= 11,
        ['arrival_Krakow']
    )
    
    # Total trip constraint: must start on day 1 and end on day 11
    problem.addConstraint(
        lambda arr_f, arr_k, arr_d: 
            min(arr_f, arr_k, arr_d) == 1 and max(arr_f + 3, arr_k + 2, arr_d + 7) == 11,
        ['arrival_Frankfurt', 'arrival_Krakow', 'arrival_Dubrovnik']
    )
    
    # No overlapping stays constraint - improved approach
    def no_overlap(arr1, arr2, arr3):
        arrivals = [arr1, arr2, arr3]
        durations_list = [3, 2, 7]
        
        # Check all pairs of cities for overlap
        for i in range(3):
            for j in range(i + 1, 3):
                a1, d1 = arrivals[i], arrivals[i] + durations_list[i]
                a2, d2 = arrivals[j], arrivals[j] + durations_list[j]
                
                # Two stays overlap if one starts before the other ends
                if not (d1 <= a2 or d2 <= a1):
                    return False
        return True
    
    problem.addConstraint(no_overlap, [
        'arrival_Frankfurt', 'arrival_Krakow', 'arrival_Dubrovnik'
    ])
    
    # Flight connectivity constraints - improved approach
    def valid_flights(arr_f, arr_k, arr_d):
        # Available flights: Frankfurt-Krakow and Dubrovnik-Frankfurt
        
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
            
            # Departure must equal next arrival (same-day travel)
            if current_dep != next_arr:
                return False
            
            # Check if flight exists between these cities
            if (current_city == 'Frankfurt' and next_city == 'Krakow') or \
               (current_city == 'Dubrovnik' and next_city == 'Frankfurt') or \
               (current_city == 'Krakow' and next_city == 'Frankfurt'):
                continue
            else:
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