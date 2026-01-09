import json
from constraint import Problem, AllDifferentConstraint

def solve_itinerary():
    # Define the problem
    problem = Problem()
    
    # Cities and their durations
    cities = ['Warsaw', 'Budapest', 'Paris', 'Riga']
    durations = {
        'Warsaw': 2,
        'Budapest': 7, 
        'Paris': 4,
        'Riga': 7
    }
    
    # Total days
    total_days = 17
    
    # Define variables for arrival day in each city
    for city in cities:
        problem.addVariable(f'{city}_arrival', range(1, total_days + 1))
    
    # All arrival days must be different
    arrival_vars = [f'{city}_arrival' for city in cities]
    problem.addConstraint(AllDifferentConstraint(), arrival_vars)
    
    # Constraint 1: Warsaw must be visited on day 1-2 (annual show)
    # Warsaw must start on day 1 or 2 and the show day (day 1 or 2) must be during the stay
    def warsaw_show_constraint(warsaw_arrival):
        # Warsaw must be visited such that either day 1 or day 2 falls within the stay
        return warsaw_arrival <= 2 and warsaw_arrival + durations['Warsaw'] - 1 >= 1
    
    problem.addConstraint(warsaw_show_constraint, ['Warsaw_arrival'])
    
    # Constraint 2: Riga wedding between day 11-17
    # Riga must be visited such that the wedding day (day 11) falls within the stay
    def riga_wedding_constraint(riga_arrival):
        return riga_arrival <= 11 and riga_arrival + durations['Riga'] - 1 >= 11
    
    problem.addConstraint(riga_wedding_constraint, ['Riga_arrival'])
    
    # Constraint 3: Total trip duration should not exceed 17 days
    def total_days_constraint(*arrivals):
        last_departure = max(arrivals[i] + durations[cities[i]] - 1 for i in range(len(cities)))
        return last_departure <= total_days
    
    problem.addConstraint(total_days_constraint, arrival_vars)
    
    # Constraint 4: Cities must be visited in a valid sequence
    # We need to ensure that cities don't overlap and form a valid travel sequence
    def valid_sequence_constraint(*arrivals):
        city_arrivals = {cities[i]: arrivals[i] for i in range(len(cities))}
        
        # Check for overlaps
        for i in range(len(cities)):
            for j in range(i + 1, len(cities)):
                city1, arr1 = cities[i], city_arrivals[cities[i]]
                city2, arr2 = cities[j], city_arrivals[cities[j]]
                dur1, dur2 = durations[city1], durations[city2]
                
                # Check if the two visits overlap
                if not (arr1 + dur1 <= arr2 or arr2 + dur2 <= arr1):
                    return False
        
        return True
    
    problem.addConstraint(valid_sequence_constraint, arrival_vars)
    
    # Constraint 5: Flight connectivity - only allowed direct flights
    flight_network = {
        'Warsaw': ['Budapest', 'Riga', 'Paris'],
        'Budapest': ['Warsaw', 'Paris'],
        'Paris': ['Budapest', 'Warsaw', 'Riga'],
        'Riga': ['Warsaw', 'Paris']
    }
    
    def flight_connectivity_constraint(*arrivals):
        city_arrivals = {cities[i]: arrivals[i] for i in range(len(cities))}
        
        # Create a sequence by arrival order
        sequence = sorted(cities, key=lambda city: city_arrivals[city])
        
        # Check that consecutive cities in the travel sequence have direct flights
        for i in range(len(sequence) - 1):
            current_city = sequence[i]
            next_city = sequence[i + 1]
            
            if next_city not in flight_network[current_city]:
                return False
        
        return True
    
    problem.addConstraint(flight_connectivity_constraint, arrival_vars)
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Create city visits with arrival days and durations
    visits = []
    for city in cities:
        visits.append({
            'city': city,
            'arrival': solution[f'{city}_arrival'],
            'duration': durations[city]
        })
    
    # Sort visits by arrival day
    visits.sort(key=lambda x: x['arrival'])
    
    # Build itinerary with day ranges
    itinerary = []
    for visit in visits:
        start_day = visit['arrival']
        end_day = start_day + visit['duration'] - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({
            "day_range": day_range,
            "place": visit['city']
        })
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))