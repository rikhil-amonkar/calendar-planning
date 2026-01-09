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
    def warsaw_show_constraint(warsaw_arrival):
        return warsaw_arrival == 1
    
    problem.addConstraint(warsaw_show_constraint, ['Warsaw_arrival'])
    
    # Constraint 2: Riga wedding between day 11-17
    def riga_wedding_constraint(riga_arrival):
        # Riga must be visited such that day 11 falls within the stay
        return riga_arrival <= 11 and riga_arrival + durations['Riga'] - 1 >= 11
    
    problem.addConstraint(riga_wedding_constraint, ['Riga_arrival'])
    
    # Constraint 3: Total trip duration should not exceed 17 days
    def total_days_constraint(*arrivals):
        last_departure = max(arrivals[i] + durations[cities[i]] - 1 for i in range(len(cities)))
        return last_departure <= total_days
    
    problem.addConstraint(total_days_constraint, arrival_vars)
    
    # Constraint 4: Cities must be visited consecutively without gaps
    # We need to ensure that when we leave one city, we arrive at the next on the same day
    def consecutive_visits_constraint(*arrivals):
        # Create a mapping of city to arrival day
        city_arrivals = {cities[i]: arrivals[i] for i in range(len(cities))}
        
        # Sort cities by arrival day to determine the sequence
        sequence = sorted(cities, key=lambda city: city_arrivals[city])
        
        # Check that each city's departure aligns with the next city's arrival
        for i in range(len(sequence) - 1):
            current_city = sequence[i]
            next_city = sequence[i + 1]
            
            departure_day = city_arrivals[current_city] + durations[current_city] - 1
            next_arrival = city_arrivals[next_city]
            
            # The next city should start the day after the current city ends
            if departure_day + 1 != next_arrival:
                return False
        
        return True
    
    problem.addConstraint(consecutive_visits_constraint, arrival_vars)
    
    # Constraint 5: Flight connectivity - only allowed direct flights
    # Flight network: Warsaw-Budapest, Warsaw-Riga, Budapest-Paris, Warsaw-Paris, Paris-Riga
    flight_network = {
        'Warsaw': ['Budapest', 'Riga', 'Paris'],
        'Budapest': ['Warsaw', 'Paris'],
        'Paris': ['Budapest', 'Warsaw', 'Riga'],
        'Riga': ['Warsaw', 'Paris']
    }
    
    def flight_connectivity_constraint(*arrivals):
        city_arrivals = {cities[i]: arrivals[i] for i in range(len(cities))}
        sequence = sorted(cities, key=lambda city: city_arrivals[city])
        
        # Check that consecutive cities in the sequence have direct flights
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