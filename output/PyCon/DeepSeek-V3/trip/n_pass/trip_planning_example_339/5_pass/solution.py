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
    # Either day 1 or day 2 must be during the Warsaw stay
    def warsaw_show_constraint(warsaw_arrival):
        warsaw_departure = warsaw_arrival + durations['Warsaw'] - 1
        return (warsaw_arrival <= 2 and warsaw_departure >= 1) or \
               (warsaw_arrival <= 1 and warsaw_departure >= 2)
    
    problem.addConstraint(warsaw_show_constraint, ['Warsaw_arrival'])
    
    # Constraint 2: Budapest must be visited between days 3-10
    def budapest_constraint(budapest_arrival):
        budapest_departure = budapest_arrival + durations['Budapest'] - 1
        return budapest_arrival >= 3 and budapest_departure <= 10
    
    problem.addConstraint(budapest_constraint, ['Budapest_arrival'])
    
    # Constraint 3: Riga wedding between day 11-17
    # Day 11 must be during the Riga stay
    def riga_wedding_constraint(riga_arrival):
        riga_departure = riga_arrival + durations['Riga'] - 1
        return riga_arrival <= 11 and riga_departure >= 11
    
    problem.addConstraint(riga_wedding_constraint, ['Riga_arrival'])
    
    # Constraint 4: Cities must be visited in a valid sequence without overlaps
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