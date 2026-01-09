import json
from constraint import Problem, AllDifferentConstraint

def solve_itinerary():
    # Define the problem
    problem = Problem()
    
    # Cities
    cities = ['Frankfurt', 'Krakow', 'Dubrovnik']
    
    # Define variables for arrival day in each city
    # We'll use arrival days to determine the itinerary
    problem.addVariable('arrival_Frankfurt', range(1, 11))
    problem.addVariable('arrival_Krakow', range(1, 11))
    problem.addVariable('arrival_Dubrovnik', range(1, 11))
    
    # Add departure days (last day in each city + 1)
    problem.addVariable('departure_Frankfurt', range(2, 12))
    problem.addVariable('departure_Krakow', range(2, 12))
    problem.addVariable('departure_Dubrovnik', range(2, 12))
    
    # Constraints for duration in each city
    def frankfurt_duration_constraint(arrival, departure):
        return (departure - arrival) == 3
    
    def krakow_duration_constraint(arrival, departure):
        return (departure - arrival) == 2
    
    def dubrovnik_duration_constraint(arrival, departure):
        return (departure - arrival) == 7
    
    problem.addConstraint(frankfurt_duration_constraint, ['arrival_Frankfurt', 'departure_Frankfurt'])
    problem.addConstraint(krakow_duration_constraint, ['arrival_Krakow', 'departure_Krakow'])
    problem.addConstraint(dubrovnik_duration_constraint, ['arrival_Dubrovnik', 'departure_Dubrovnik'])
    
    # Constraint: Krakow wedding between day 9 and 10
    # This means arrival_Krakow <= 9 and departure_Krakow >= 10
    def krakow_wedding_constraint(arrival, departure):
        return arrival <= 9 and departure >= 10
    
    problem.addConstraint(krakow_wedding_constraint, ['arrival_Krakow', 'departure_Krakow'])
    
    # Constraint: No overlapping stays in different cities
    # A city's departure day must equal the next city's arrival day
    def no_overlap_constraint(arrival_f, departure_f, arrival_k, departure_k, arrival_d, departure_d):
        # Check all possible transitions based on flight availability
        # Direct flights: Frankfurt-Krakow, Dubrovnik-Frankfurt
        transitions = []
        
        # From Frankfurt to Krakow
        if departure_f == arrival_k:
            transitions.append(('Frankfurt', 'Krakow'))
        
        # From Krakow to Frankfurt  
        if departure_k == arrival_f:
            transitions.append(('Krakow', 'Frankfurt'))
        
        # From Dubrovnik to Frankfurt
        if departure_d == arrival_f:
            transitions.append(('Dubrovnik', 'Frankfurt'))
        
        # From Frankfurt to Dubrovnik
        if departure_f == arrival_d:
            transitions.append(('Frankfurt', 'Dubrovnik'))
        
        # We need exactly 2 transitions for 3 cities
        if len(transitions) != 2:
            return False
        
        # Check if transitions form a valid path visiting all cities
        visited = set()
        current = None
        
        # Find starting city (one that is never arrived at from another city)
        all_arrivals = [arrival_f, arrival_k, arrival_d]
        all_departures = [departure_f, departure_k, departure_d]
        
        # The trip must start on day 1 and end on day 11 (since we have 10 days)
        if min(all_arrivals) != 1 or max(all_departures) != 11:
            return False
            
        return True
    
    problem.addConstraint(no_overlap_constraint, [
        'arrival_Frankfurt', 'departure_Frankfurt',
        'arrival_Krakow', 'departure_Krakow', 
        'arrival_Dubrovnik', 'departure_Dubrovnik'
    ])
    
    # Constraint: All arrival days must be different since we can't be in multiple cities simultaneously
    # except for transition days where we're counted in both cities
    def valid_schedule_constraint(arrival_f, departure_f, arrival_k, departure_k, arrival_d, departure_d):
        # Create day assignments for each city
        frankfurt_days = set(range(arrival_f, departure_f))
        krakow_days = set(range(arrival_k, departure_k))
        dubrovnik_days = set(range(arrival_d, departure_d))
        
        # On any given day, we should be in exactly one city
        # Except transition days where we're counted in both cities
        all_days = set(range(1, 11))
        
        for day in all_days:
            cities_on_day = []
            if day in frankfurt_days:
                cities_on_day.append('Frankfurt')
            if day in krakow_days:
                cities_on_day.append('Krakow') 
            if day in dubrovnik_days:
                cities_on_day.append('Dubrovnik')
                
            # Should be in exactly one city on non-transition days
            # On transition days, we might be in 2 cities
            if len(cities_on_day) == 0:
                return False
                
        return True
    
    problem.addConstraint(valid_schedule_constraint, [
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
    
    # Build the itinerary
    itinerary = []
    
    # Create day ranges for each city stay
    city_stays = [
        ('Frankfurt', solution['arrival_Frankfurt'], solution['departure_Frankfurt']),
        ('Krakow', solution['arrival_Krakow'], solution['departure_Krakow']),
        ('Dubrovnik', solution['arrival_Dubrovnik'], solution['departure_Dubrovnik'])
    ]
    
    # Sort by arrival day
    city_stays.sort(key=lambda x: x[1])
    
    for city, arrival, departure in city_stays:
        if arrival == departure - 1:
            day_range = f"Day {arrival}"
        else:
            day_range = f"Day {arrival}-{departure-1}"
        itinerary.append({
            "day_range": day_range,
            "place": city
        })
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))