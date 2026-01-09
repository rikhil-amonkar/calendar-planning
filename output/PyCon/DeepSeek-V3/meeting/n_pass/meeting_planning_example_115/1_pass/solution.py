import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes
    travel_times = {
        ('Richmond District', 'Pacific Heights'): 10,
        ('Richmond District', 'Marina District'): 9,
        ('Pacific Heights', 'Richmond District'): 12,
        ('Pacific Heights', 'Marina District'): 6,
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'Pacific Heights'): 7
    }
    
    # Convert all times to minutes since 9:00 AM (540 minutes)
    start_time_total_minutes = 540  # 9:00 AM
    
    # Convert friend availability to minutes since 9:00 AM
    jessica_start = 15 * 60 + 30  # 3:30 PM = 930 minutes
    jessica_end = 16 * 60 + 45    # 4:45 PM = 1005 minutes
    carol_start = 11 * 60 + 30    # 11:30 AM = 690 minutes
    carol_end = 15 * 60           # 3:00 PM = 900 minutes
    
    # Meeting duration requirements in minutes
    jessica_min_duration = 45
    carol_min_duration = 60
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start times and durations for each meeting
    # We'll plan the order: either Carol then Jessica, or Jessica then Carol
    # But since Jessica is only available late, Carol first makes more sense
    
    # Let's try Carol first, then Jessica
    # carol_start_time, carol_duration, jessica_start_time, jessica_duration
    problem.addVariable('carol_start', range(carol_start, carol_end - carol_min_duration + 1))
    problem.addVariable('carol_duration', range(carol_min_duration, carol_end - carol_start + 1))
    problem.addVariable('jessica_start', range(jessica_start, jessica_end - jessica_min_duration + 1))
    problem.addVariable('jessica_duration', range(jessica_min_duration, jessica_end - jessica_start + 1))
    
    # Constraints
    def travel_and_time_constraint(cs, cd, js, jd):
        # Carol meeting must end before Jessica meeting starts, accounting for travel
        carol_end = cs + cd
        travel_to_jessica = travel_times[('Marina District', 'Pacific Heights')]
        
        # Check if we can travel from Carol to Jessica
        if carol_end + travel_to_jessica > js:
            return False
        
        # Check if we have enough time to get from start to Carol
        travel_to_carol = travel_times[('Richmond District', 'Marina District')]
        if start_time_total_minutes + travel_to_carol > cs:
            return False
            
        return True
    
    problem.addConstraint(travel_and_time_constraint, ['carol_start', 'carol_duration', 'jessica_start', 'jessica_duration'])
    
    # Objective: maximize total meeting time
    solutions = problem.getSolutions()
    
    if not solutions:
        # Try alternative: just meet one person
        problem_single = constraint.Problem()
        
        # Try meeting Carol only
        problem_single.addVariable('carol_start', range(carol_start, carol_end - carol_min_duration + 1))
        problem_single.addVariable('carol_duration', range(carol_min_duration, carol_end - carol_start + 1))
        
        def carol_only_constraint(cs, cd):
            travel_to_carol = travel_times[('Richmond District', 'Marina District')]
            return start_time_total_minutes + travel_to_carol <= cs
        
        problem_single.addConstraint(carol_only_constraint, ['carol_start', 'carol_duration'])
        carol_solutions = problem_single.getSolutions()
        
        if carol_solutions:
            # Find solution with maximum duration for Carol
            best_carol = max(carol_solutions, key=lambda x: x['carol_duration'])
            
            # Create itinerary
            itinerary = []
            carol_start_minutes = best_carol['carol_start']
            carol_end_minutes = carol_start_minutes + best_carol['carol_duration']
            
            itinerary.append({
                "action": "meet",
                "location": "Marina District",
                "person": "Carol",
                "start_time": minutes_to_time(carol_start_minutes),
                "end_time": minutes_to_time(carol_end_minutes)
            })
            
            result = {"itinerary": itinerary}
            print(json.dumps(result, indent=2))
            return
        
        # If no solution found, return empty itinerary
        result = {"itinerary": []}
        print(json.dumps(result, indent=2))
        return
    
    # Find solution with maximum total meeting time
    best_solution = max(solutions, key=lambda x: x['carol_duration'] + x['jessica_duration'])
    
    # Create itinerary
    itinerary = []
    
    # Carol meeting
    carol_start_minutes = best_solution['carol_start']
    carol_end_minutes = carol_start_minutes + best_solution['carol_duration']
    
    itinerary.append({
        "action": "meet",
        "location": "Marina District",
        "person": "Carol",
        "start_time": minutes_to_time(carol_start_minutes),
        "end_time": minutes_to_time(carol_end_minutes)
    })
    
    # Jessica meeting
    jessica_start_minutes = best_solution['jessica_start']
    jessica_end_minutes = jessica_start_minutes + best_solution['jessica_duration']
    
    itinerary.append({
        "action": "meet",
        "location": "Pacific Heights",
        "person": "Jessica",
        "start_time": minutes_to_time(jessica_start_minutes),
        "end_time": minutes_to_time(jessica_end_minutes)
    })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

def minutes_to_time(total_minutes):
    """Convert total minutes since midnight to time string"""
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

if __name__ == "__main__":
    main()