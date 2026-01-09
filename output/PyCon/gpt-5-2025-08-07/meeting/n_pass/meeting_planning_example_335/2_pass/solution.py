from constraint import Problem
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
    
    # Friend constraints (location, available_start, available_end, min_duration)
    friends = {
        'Helen': ('North Beach', time_to_minutes('9:00'), time_to_minutes('17:00'), 15),
        'Betty': ('Financial District', time_to_minutes('19:00'), time_to_minutes('21:45'), 90),
        'Amanda': ('Alamo Square', time_to_minutes('19:45'), time_to_minutes('21:00'), 60),
        'Kevin': ('Mission District', time_to_minutes('10:45'), time_to_minutes('14:45'), 45)
    }
    
    # Try different meeting orders to find a feasible schedule
    from itertools import permutations
    
    best_schedule = None
    max_meetings = 0
    
    for order in permutations(friends.keys()):
        # Create a fresh problem for this order
        problem = Problem()
        
        # Add variables with more flexible time ranges
        for friend in order:
            location, available_start, available_end, min_duration = friends[friend]
            # Allow some buffer before and after the stated availability
            problem.addVariable(f"{friend}_start", range(available_start, available_end - min_duration + 1))
            problem.addVariable(f"{friend}_duration", [min_duration])
        
        # Add constraints for this order
        for i in range(len(order) - 1):
            friend1 = order[i]
            friend2 = order[i + 1]
            
            loc1 = friends[friend1][0]
            loc2 = friends[friend2][0]
            travel_time = travel_times.get((loc1, loc2), 60)
            
            def meeting_sequence(f1_start, f1_dur, f2_start, f2_dur):
                return f1_start + f1_dur + travel_time <= f2_start
            
            problem.addConstraint(
                meeting_sequence,
                [f"{friend1}_start", f"{friend1}_duration", f"{friend2}_start", f"{friend2}_duration"]
            )
        
        # Constraint: first meeting must be after travel from Pacific Heights
        first_friend = order[0]
        first_location = friends[first_friend][0]
        travel_to_first = travel_times.get(('Pacific Heights', first_location), 60)
        
        def first_meeting_constraint(start_time):
            return start_time >= time_to_minutes('9:00') + travel_to_first
        
        problem.addConstraint(first_meeting_constraint, [f"{first_friend}_start"])
        
        # Constraint: last meeting must end before midnight (or reasonable time)
        last_friend = order[-1]
        last_location = friends[last_friend][0]
        _, _, last_available_end, last_min_duration = friends[last_friend]
        
        def last_meeting_constraint(start_time, duration):
            return start_time + duration <= last_available_end
        
        problem.addConstraint(last_meeting_constraint, [f"{last_friend}_start", f"{last_friend}_duration"])
        
        # Find solution
        solutions = problem.getSolutions()
        
        if solutions:
            scheduled_count = len(order)
            if scheduled_count > max_meetings:
                max_meetings = scheduled_count
                best_schedule = (order, solutions[0])
                # If we found a schedule with all 4 friends, we can stop
                if max_meetings == 4:
                    break
    
    # Build itinerary
    itinerary = []
    
    if best_schedule:
        order, solution = best_schedule
        
        current_time = time_to_minutes('9:00')
        current_location = 'Pacific Heights'
        
        for i, friend in enumerate(order):
            friend_location = friends[friend][0]
            friend_start = solution[f"{friend}_start"]
            friend_duration = solution[f"{friend}_duration"]
            
            # Add travel if needed
            if current_location != friend_location:
                travel_time = travel_times.get((current_location, friend_location), 60)
                
                # If we arrive early, we might need to wait
                arrival_time = current_time + travel_time
                if arrival_time < friend_start:
                    # Add travel segment
                    itinerary.append({
                        "action": "travel",
                        "location": friend_location,
                        "person": "",
                        "start_time": minutes_to_time(current_time),
                        "end_time": minutes_to_time(arrival_time)
                    })
                    
                    # Add waiting time if needed
                    if arrival_time < friend_start:
                        itinerary.append({
                            "action": "wait",
                            "location": friend_location,
                            "person": "",
                            "start_time": minutes_to_time(arrival_time),
                            "end_time": minutes_to_time(friend_start)
                        })
                else:
                    # Travel directly to meeting
                    itinerary.append({
                        "action": "travel",
                        "location": friend_location,
                        "person": "",
                        "start_time": minutes_to_time(current_time),
                        "end_time": minutes_to_time(friend_start)
                    })
            
            # Add meeting
            itinerary.append({
                "action": "meet",
                "location": friend_location,
                "person": friend,
                "start_time": minutes_to_time(friend_start),
                "end_time": minutes_to_time(friend_start + friend_duration)
            })
            
            current_time = friend_start + friend_duration
            current_location = friend_location
    
    # If no complete schedule found, try to schedule a subset
    if not best_schedule:
        # Try scheduling just 3 friends
        from itertools import combinations
        for num_friends in range(3, 0, -1):
            for friend_subset in combinations(friends.keys(), num_friends):
                for order in permutations(friend_subset):
                    problem = Problem()
                    
                    for friend in order:
                        location, available_start, available_end, min_duration = friends[friend]
                        problem.addVariable(f"{friend}_start", range(available_start, available_end - min_duration + 1))
                        problem.addVariable(f"{friend}_duration", [min_duration])
                    
                    # Add constraints
                    for i in range(len(order) - 1):
                        friend1 = order[i]
                        friend2 = order[i + 1]
                        loc1 = friends[friend1][0]
                        loc2 = friends[friend2][0]
                        travel_time = travel_times.get((loc1, loc2), 60)
                        
                        def meeting_sequence(f1_start, f1_dur, f2_start, f2_dur):
                            return f1_start + f1_dur + travel_time <= f2_start
                        
                        problem.addConstraint(
                            meeting_sequence,
                            [f"{friend1}_start", f"{friend1}_duration", f"{friend2}_start", f"{friend2}_duration"]
                        )
                    
                    # First meeting constraint
                    first_friend = order[0]
                    first_location = friends[first_friend][0]
                    travel_to_first = travel_times.get(('Pacific Heights', first_location), 60)
                    
                    def first_meeting_constraint(start_time):
                        return start_time >= time_to_minutes('9:00') + travel_to_first
                    
                    problem.addConstraint(first_meeting_constraint, [f"{first_friend}_start"])
                    
                    solutions = problem.getSolutions()
                    if solutions:
                        best_schedule = (order, solutions[0])
                        break
                if best_schedule:
                    break
            if best_schedule:
                break
        
        # Build itinerary for partial schedule
        if best_schedule:
            order, solution = best_schedule
            
            current_time = time_to_minutes('9:00')
            current_location = 'Pacific Heights'
            
            for i, friend in enumerate(order):
                friend_location = friends[friend][0]
                friend_start = solution[f"{friend}_start"]
                friend_duration = solution[f"{friend}_duration"]
                
                # Add travel if needed
                if current_location != friend_location:
                    travel_time = travel_times.get((current_location, friend_location), 60)
                    itinerary.append({
                        "action": "travel",
                        "location": friend_location,
                        "person": "",
                        "start_time": minutes_to_time(current_time),
                        "end_time": minutes_to_time(current_time + travel_time)
                    })
                    current_time += travel_time
                
                # Add meeting
                itinerary.append({
                    "action": "meet",
                    "location": friend_location,
                    "person": friend,
                    "start_time": minutes_to_time(friend_start),
                    "end_time": minutes_to_time(friend_start + friend_duration)
                })
                
                current_time = friend_start + friend_duration
                current_location = friend_location
    
    # Output as JSON
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()