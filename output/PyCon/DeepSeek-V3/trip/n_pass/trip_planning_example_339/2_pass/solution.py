import json
from constraint import Problem, AllDifferentConstraint

def solve_itinerary():
    # Define the problem
    problem = Problem()
    
    # Cities
    cities = ['Warsaw', 'Budapest', 'Paris', 'Riga']
    
    # Total days
    total_days = 17
    
    # Define variables for arrival day in each city
    # We'll use arrival days to determine the sequence
    problem.addVariable('Warsaw_arrival', range(1, total_days + 1))
    problem.addVariable('Budapest_arrival', range(1, total_days + 1))
    problem.addVariable('Paris_arrival', range(1, total_days + 1))
    problem.addVariable('Riga_arrival', range(1, total_days + 1))
    
    # Duration constraints
    warsaw_duration = 2
    budapest_duration = 7
    paris_duration = 4
    riga_duration = 7
    
    # Add constraint: all arrival days must be different
    problem.addConstraint(AllDifferentConstraint(), 
                         ['Warsaw_arrival', 'Budapest_arrival', 'Paris_arrival', 'Riga_arrival'])
    
    # Add constraint: Warsaw must be visited on day 1-2 (annual show)
    def warsaw_show_constraint(warsaw_arrival):
        return warsaw_arrival == 1
    
    problem.addConstraint(warsaw_show_constraint, ['Warsaw_arrival'])
    
    # Add constraint: Riga wedding between day 11-17
    def riga_wedding_constraint(riga_arrival):
        # Riga must be visited such that day 11 falls within the stay
        return riga_arrival <= 11 and riga_arrival + riga_duration - 1 >= 11
    
    problem.addConstraint(riga_wedding_constraint, ['Riga_arrival'])
    
    # Add constraint: total days should not exceed 17
    def total_days_constraint(w, b, p, r):
        last_day = max(
            w + warsaw_duration - 1,
            b + budapest_duration - 1,
            p + paris_duration - 1,
            r + riga_duration - 1
        )
        return last_day <= total_days
    
    problem.addConstraint(total_days_constraint, 
                         ['Warsaw_arrival', 'Budapest_arrival', 'Paris_arrival', 'Riga_arrival'])
    
    # Add flight connectivity constraints - FIXED VERSION
    def can_fly_between(arrival1, arrival2, duration1, duration2):
        # Check if it's possible to fly directly between two cities
        # Either city1 ends when city2 begins, or city2 ends when city1 begins
        return (arrival1 + duration1 == arrival2) or (arrival2 + duration2 == arrival1)
    
    # Warsaw-Budapest direct flight
    problem.addConstraint(
        lambda w, b: can_fly_between(w, b, warsaw_duration, budapest_duration),
        ['Warsaw_arrival', 'Budapest_arrival']
    )
    
    # Warsaw-Riga direct flight  
    problem.addConstraint(
        lambda w, r: can_fly_between(w, r, warsaw_duration, riga_duration),
        ['Warsaw_arrival', 'Riga_arrival']
    )
    
    # Budapest-Paris direct flight
    problem.addConstraint(
        lambda b, p: can_fly_between(b, p, budapest_duration, paris_duration),
        ['Budapest_arrival', 'Paris_arrival']
    )
    
    # Warsaw-Paris direct flight
    problem.addConstraint(
        lambda w, p: can_fly_between(w, p, warsaw_duration, paris_duration),
        ['Warsaw_arrival', 'Paris_arrival']
    )
    
    # Paris-Riga direct flight
    problem.addConstraint(
        lambda p, r: can_fly_between(p, r, paris_duration, riga_duration),
        ['Paris_arrival', 'Riga_arrival']
    )
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Create city visits with arrival days and durations
    visits = [
        {'city': 'Warsaw', 'arrival': solution['Warsaw_arrival'], 'duration': warsaw_duration},
        {'city': 'Budapest', 'arrival': solution['Budapest_arrival'], 'duration': budapest_duration},
        {'city': 'Paris', 'arrival': solution['Paris_arrival'], 'duration': paris_duration},
        {'city': 'Riga', 'arrival': solution['Riga_arrival'], 'duration': riga_duration}
    ]
    
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