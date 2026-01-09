from constraint import Problem, AllDifferentConstraint
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes (from -> to)
    travel_times = {
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Financial District'): 13,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Mission District'): 15,
        ('North Beach', 'Pacific Heights'): 8,
        ('North Beach', 'Financial District'): 8,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Mission District'): 18,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'North Beach'): 7,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'Mission District'): 17,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Financial District'): 17,
        ('Alamo Square', 'Mission District'): 10,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'North Beach'): 17,
        ('Mission District', 'Financial District'): 17,
        ('Mission District', 'Alamo Square'): 11
    }
    
    # Convert all times to minutes since midnight
    start_time = time_to_minutes('9:00')
    
    # Friend constraints (location, available_start, available_end, min_duration)
    friends = {
        'Helen': ('North Beach', time_to_minutes('9:00'), time_to_minutes('17:00'), 15),
        'Betty': ('Financial District', time_to_minutes('19:00'), time_to_minutes('21:45'), 90),
        'Amanda': ('Alamo Square', time_to_minutes('19:45'), time_to_minutes('21:00'), 60),
        'Kevin': ('Mission District', time_to_minutes('10:45'), time_to_minutes('14:45'), 45)
    }
    
    # Create constraint problem
    problem = Problem()
    
    # Variables: start time for each meeting
    friend_names = list(friends.keys())
    for friend in friend_names:
        location, available_start, available_end, min_duration = friends[friend]
        problem.addVariable(f"{friend}_start", range(available_start, available_end - min_duration + 1))
        problem.addVariable(f"{friend}_duration", [min_duration])
    
    # Constraint: all meetings must be scheduled
    # We'll try to schedule all friends first, then relax constraints if needed
    
    # Add travel time constraints between consecutive meetings
    # We need to consider all possible orders
    from itertools import permutations
    
    def add_order_constraints(order):
        for i in range(len(order) - 1):
            friend1 = order[i]
            friend2 = order[i + 1]
            
            loc1 = friends[friend1][0]
            loc2 = friends[friend2][0]
            travel_time = travel_times.get((loc1, loc2), 60)  # Default high if not found
            
            def meeting_sequence(f1_start, f1_dur, f2_start, f2_dur):
                return f1_start + f1_dur + travel_time <= f2_start
            
            problem.addConstraint(
                meeting_sequence,
                [f"{friend1}_start", f"{friend1}_duration", f"{friend2}_start", f"{friend2}_duration"]
            )
    
    # Try different meeting orders to find a feasible schedule
    best_schedule = None
    max_meetings = 0
    
    for order in permutations(friend_names):
        # Create a fresh problem for this order
        temp_problem = Problem()
        
        # Add variables
        for friend in friend_names:
            location, available_start, available_end, min_duration = friends[friend]
            temp_problem.addVariable(f"{friend}_start", range(available_start, available_end - min_duration + 1))
            temp_problem.addVariable(f"{friend}_duration", [min_duration])
        
        # Add constraints for this order
        for i in range(len(order) - 1):
            friend1 = order[i]
            friend2 = order[i + 1]
            
            loc1 = friends[friend1][0]
            loc2 = friends[friend2][0]
            travel_time = travel_times.get((loc1, loc2), 60)
            
            def meeting_sequence(f1_start, f1_dur, f2_start, f2_dur):
                return f1_start + f1_dur + travel_time <= f2_start
            
            temp_problem.addConstraint(
                meeting_sequence,
                [f"{friend1}_start", f"{friend1}_duration", f"{friend2}_start", f"{friend2}_duration"]
            )
        
        # Also add constraint that first meeting must be after travel from Pacific Heights
        first_friend = order[0]
        first_location = friends[first_friend][0]
        travel_to_first = travel_times.get(('Pacific Heights', first_location), 60)
        
        def first_meeting_constraint(start_time):
            return start_time >= time_to_minutes('9:00') + travel_to_first
        
        temp_problem.addConstraint(first_meeting_constraint, [f"{first_friend}_start"])
        
        # Find solution
        solutions = temp_problem.getSolutions()
        
        if solutions:
            # Count how many meetings we can schedule
            scheduled_count = len(order)
            
            if scheduled_count > max_meetings:
                max_meetings = scheduled_count
                best_schedule = (order, solutions[0])
    
    # Build itinerary
    itinerary = []
    
    if best_schedule:
        order, solution = best_schedule
        
        # Add initial travel to first meeting
        first_friend = order[0]
        first_location = friends[first_friend][0]
        travel_to_first = travel_times.get(('Pacific Heights', first_location), 60)
        
        if solution[f"{first_friend}_start"] > time_to_minutes('9:00') + travel_to_first:
            itinerary.append({
                "action": "travel",
                "location": first_location,
                "person": "",
                "start_time": minutes_to_time(time_to_minutes('9:00')),
                "end_time": minutes_to_time(time_to_minutes('9:00') + travel_to_first)
            })
        
        # Add meetings
        for i, friend in enumerate(order):
            start_time = solution[f"{friend}_start"]
            duration = solution[f"{friend}_duration"]
            location = friends[friend][0]
            
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": friend,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(start_time + duration)
            })
            
            # Add travel to next meeting if not last
            if i < len(order) - 1:
                next_friend = order[i + 1]
                next_location = friends[next_friend][0]
                travel_time = travel_times.get((location, next_location), 60)
                
                itinerary.append({
                    "action": "travel",
                    "location": next_location,
                    "person": "",
                    "start_time": minutes_to_time(start_time + duration),
                    "end_time": minutes_to_time(start_time + duration + travel_time)
                })
    
    # Output as JSON
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()