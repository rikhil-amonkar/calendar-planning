from constraint import Problem
import json

def main():
    # Define travel times in minutes
    travel_times = {
        ('Pacific Heights', 'Presidio'): 11,
        ('Pacific Heights', 'Marina District'): 6,
        ('Presidio', 'Pacific Heights'): 11,
        ('Presidio', 'Marina District'): 10,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'Presidio'): 10,
    }
    
    # Convert all times to minutes since 9:00 (540 minutes)
    start_of_day = 9 * 60  # 9:00 AM
    
    # Jason's availability at Presidio
    jason_start = 10 * 60      # 10:00 AM
    jason_end = 16 * 60 + 15   # 4:15 PM (16:15)
    jason_min_duration = 90    # 90 minutes
    
    # Kenneth's availability at Marina District
    kenneth_start = 15 * 60 + 30  # 3:30 PM (15:30)
    kenneth_end = 16 * 60 + 45    # 4:45 PM (16:45)
    kenneth_min_duration = 45     # 45 minutes
    
    # Create constraint problem
    problem = Problem()
    
    # Define variables for meeting times (in minutes since 9:00)
    # Jason meeting start and end times
    problem.addVariable("jason_start", range(jason_start, jason_end - jason_min_duration + 1))
    problem.addVariable("jason_end", range(jason_start + jason_min_duration, jason_end + 1))
    
    # Kenneth meeting start and end times
    problem.addVariable("kenneth_start", range(kenneth_start, kenneth_end - kenneth_min_duration + 1))
    problem.addVariable("kenneth_end", range(kenneth_start + kenneth_min_duration, kenneth_end + 1))
    
    # Add duration constraints
    problem.addConstraint(lambda s, e: e - s >= jason_min_duration, ["jason_start", "jason_end"])
    problem.addConstraint(lambda s, e: e - s >= kenneth_min_duration, ["kenneth_start", "kenneth_end"])
    
    # Add travel time constraints
    def travel_constraint(js, je, ks, ke):
        # Check if we can travel from Jason to Kenneth
        if je <= ks:  # Meet Jason first, then Kenneth
            travel_time = travel_times[('Presidio', 'Marina District')]
            return ks >= je + travel_time
        else:  # Meet Kenneth first, then Jason
            travel_time = travel_times[('Marina District', 'Presidio')]
            return js >= ke + travel_time
    
    problem.addConstraint(travel_constraint, ["jason_start", "jason_end", "kenneth_start", "kenneth_end"])
    
    # Define objective function to maximize total meeting time
    def objective(js, je, ks, ke):
        jason_duration = je - js
        kenneth_duration = ke - ks
        return jason_duration + kenneth_duration
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found with both meetings, try just one meeting
        problem_single = Problem()
        
        # Try Jason only
        problem_single.addVariable("jason_start", range(jason_start, jason_end - jason_min_duration + 1))
        problem_single.addVariable("jason_end", range(jason_start + jason_min_duration, jason_end + 1))
        problem_single.addConstraint(lambda s, e: e - s >= jason_min_duration, ["jason_start", "jason_end"])
        
        jason_solutions = problem_single.getSolutions()
        
        if jason_solutions:
            # Pick the solution with maximum duration for Jason
            best_solution = max(jason_solutions, key=lambda sol: sol["jason_end"] - sol["jason_start"])
            itinerary = [
                {
                    "action": "meet",
                    "location": "Presidio",
                    "person": "Jason",
                    "start_time": minutes_to_time(best_solution["jason_start"]),
                    "end_time": minutes_to_time(best_solution["jason_end"])
                }
            ]
        else:
            # Try Kenneth only
            problem_single = Problem()
            problem_single.addVariable("kenneth_start", range(kenneth_start, kenneth_end - kenneth_min_duration + 1))
            problem_single.addVariable("kenneth_end", range(kenneth_start + kenneth_min_duration, kenneth_end + 1))
            problem_single.addConstraint(lambda s, e: e - s >= kenneth_min_duration, ["kenneth_start", "kenneth_end"])
            
            kenneth_solutions = problem_single.getSolutions()
            
            if kenneth_solutions:
                # Pick the solution with maximum duration for Kenneth
                best_solution = max(kenneth_solutions, key=lambda sol: sol["kenneth_end"] - sol["kenneth_start"])
                itinerary = [
                    {
                        "action": "meet",
                        "location": "Marina District",
                        "person": "Kenneth",
                        "start_time": minutes_to_time(best_solution["kenneth_start"]),
                        "end_time": minutes_to_time(best_solution["kenneth_end"])
                    }
                ]
            else:
                itinerary = []
    else:
        # Find the solution with maximum total meeting time
        best_solution = max(solutions, key=lambda sol: objective(sol["jason_start"], sol["jason_end"], sol["kenneth_start"], sol["kenneth_end"]))
        
        # Determine the order of meetings
        if best_solution["jason_end"] <= best_solution["kenneth_start"]:
            # Jason first, then Kenneth
            itinerary = [
                {
                    "action": "meet",
                    "location": "Presidio",
                    "person": "Jason",
                    "start_time": minutes_to_time(best_solution["jason_start"]),
                    "end_time": minutes_to_time(best_solution["jason_end"])
                },
                {
                    "action": "meet",
                    "location": "Marina District",
                    "person": "Kenneth",
                    "start_time": minutes_to_time(best_solution["kenneth_start"]),
                    "end_time": minutes_to_time(best_solution["kenneth_end"])
                }
            ]
        else:
            # Kenneth first, then Jason
            itinerary = [
                {
                    "action": "meet",
                    "location": "Marina District",
                    "person": "Kenneth",
                    "start_time": minutes_to_time(best_solution["kenneth_start"]),
                    "end_time": minutes_to_time(best_solution["kenneth_end"])
                },
                {
                    "action": "meet",
                    "location": "Presidio",
                    "person": "Jason",
                    "start_time": minutes_to_time(best_solution["jason_start"]),
                    "end_time": minutes_to_time(best_solution["jason_end"])
                }
            ]
    
    # Output the result as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string in 24-hour format"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

if __name__ == "__main__":
    main()