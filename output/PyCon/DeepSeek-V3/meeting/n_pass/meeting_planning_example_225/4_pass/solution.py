def main():
    # Travel times in minutes
    travel_times = {
        ('Sunset District', 'North Beach'): 29,
        ('Sunset District', 'Union Square'): 30,
        ('Sunset District', 'Alamo Square'): 17,
        ('North Beach', 'Sunset District'): 27,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'Alamo Square'): 16,
        ('Union Square', 'Sunset District'): 26,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Alamo Square'): 15,
        ('Alamo Square', 'Sunset District'): 16,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Union Square'): 14
    }
    
    # Convert all times to minutes since 9:00 AM
    def time_to_minutes(time_str):
        time_obj = datetime.strptime(time_str, '%H:%M')
        base_time = datetime.strptime('9:00', '%H:%M')
        delta = time_obj - base_time
        return int(delta.total_seconds() / 60)
    
    def minutes_to_time(minutes):
        base_time = datetime.strptime('9:00', '%H:%M')
        result_time = base_time + timedelta(minutes=minutes)
        return result_time.strftime('%H:%M')
    
    # Friend constraints
    sarah_available_start = time_to_minutes('16:00')  # 4:00 PM
    sarah_available_end = time_to_minutes('18:15')    # 6:15 PM
    sarah_min_duration = 60
    
    jeffrey_available_start = time_to_minutes('15:00')  # 3:00 PM
    jeffrey_available_end = time_to_minutes('22:00')    # 10:00 PM
    jeffrey_min_duration = 75
    
    brian_available_start = time_to_minutes('16:00')   # 4:00 PM
    brian_available_end = time_to_minutes('17:30')     # 5:30 PM
    brian_min_duration = 75
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start times and durations for each friend
    # We'll use discrete time intervals of 5 minutes for efficiency
    time_step = 5
    
    # Sarah meeting variables
    sarah_start_range = list(range(sarah_available_start, sarah_available_end - sarah_min_duration + 1, time_step))
    sarah_duration_range = list(range(sarah_min_duration, sarah_available_end - sarah_available_start + 1, time_step))
    
    # Jeffrey meeting variables  
    jeffrey_start_range = list(range(jeffrey_available_start, jeffrey_available_end - jeffrey_min_duration + 1, time_step))
    jeffrey_duration_range = list(range(jeffrey_min_duration, jeffrey_available_end - jeffrey_available_start + 1, time_step))
    
    # Brian meeting variables
    brian_start_range = list(range(brian_available_start, brian_available_end - brian_min_duration + 1, time_step))
    brian_duration_range = list(range(brian_min_duration, brian_available_end - brian_available_start + 1, time_step))
    
    # Add variables
    problem.addVariable('sarah_start', sarah_start_range)
    problem.addVariable('sarah_duration', sarah_duration_range)
    problem.addVariable('jeffrey_start', jeffrey_start_range)
    problem.addVariable('jeffrey_duration', jeffrey_duration_range)
    problem.addVariable('brian_start', brian_start_range)
    problem.addVariable('brian_duration', brian_duration_range)
    
    # Helper functions
    def sarah_end(start, duration):
        return start + duration
    
    def jeffrey_end(start, duration):
        return start + duration
    
    def brian_end(start, duration):
        return start + duration
    
    # Constraints for each friend's availability
    problem.addConstraint(lambda start, duration: start + duration <= sarah_available_end, ['sarah_start', 'sarah_duration'])
    problem.addConstraint(lambda start, duration: start + duration <= jeffrey_available_end, ['jeffrey_start', 'jeffrey_duration'])
    problem.addConstraint(lambda start, duration: start + duration <= brian_available_end, ['brian_start', 'brian_duration'])
    
    # Travel time constraints between meetings
    def no_overlap_with_travel(s1, d1, s2, d2, travel_time):
        e1 = s1 + d1
        e2 = s2 + d2
        # Either meeting 1 ends before meeting 2 starts minus travel time
        # Or meeting 2 ends before meeting 1 starts minus travel time
        return (e1 <= s2 - travel_time) or (e2 <= s1 - travel_time)
    
    # Since we can only be in one place at a time, we need to sequence the meetings
    # Let's try different orders and pick the best one
    
    best_solution = None
    best_total_time = 0
    
    # Try different meeting orders
    meeting_orders = [
        ['sarah', 'jeffrey', 'brian'],
        ['sarah', 'brian', 'jeffrey'],
        ['jeffrey', 'sarah', 'brian'],
        ['jeffrey', 'brian', 'sarah'],
        ['brian', 'sarah', 'jeffrey'],
        ['brian', 'jeffrey', 'sarah']
    ]
    
    for order in meeting_orders:
        temp_problem = constraint.Problem()
        
        # Add the same variables
        temp_problem.addVariable('sarah_start', sarah_start_range)
        temp_problem.addVariable('sarah_duration', sarah_duration_range)
        temp_problem.addVariable('jeffrey_start', jeffrey_start_range)
        temp_problem.addVariable('jeffrey_duration', jeffrey_duration_range)
        temp_problem.addVariable('brian_start', brian_start_range)
        temp_problem.addVariable('brian_duration', brian_duration_range)
        
        # Availability constraints
        temp_problem.addConstraint(lambda start, duration: start + duration <= sarah_available_end, ['sarah_start', 'sarah_duration'])
        temp_problem.addConstraint(lambda start, duration: start + duration <= jeffrey_available_end, ['jeffrey_start', 'jeffrey_duration'])
        temp_problem.addConstraint(lambda start, duration: start + duration <= brian_available_end, ['brian_start', 'brian_duration'])
        
        # Order-specific travel constraints
        if order == ['sarah', 'jeffrey', 'brian']:
            temp_problem.addConstraint(
                lambda s_s, s_d, j_s, j_d: s_s + s_d + travel_times[('North Beach', 'Union Square')] <= j_s,
                ['sarah_start', 'sarah_duration', 'jeffrey_start', 'jeffrey_duration']
            )
            temp_problem.addConstraint(
                lambda j_s, j_d, b_s, b_d: j_s + j_d + travel_times[('Union Square', 'Alamo Square')] <= b_s,
                ['jeffrey_start', 'jeffrey_duration', 'brian_start', 'brian_duration']
            )
        elif order == ['sarah', 'brian', 'jeffrey']:
            temp_problem.addConstraint(
                lambda s_s, s_d, b_s, b_d: s_s + s_d + travel_times[('North Beach', 'Alamo Square')] <= b_s,
                ['sarah_start', 'sarah_duration', 'brian_start', 'brian_duration']
            )
            temp_problem.addConstraint(
                lambda b_s, b_d, j_s, j_d: b_s + b_d + travel_times[('Alamo Square', 'Union Square')] <= j_s,
                ['brian_start', 'brian_duration', 'jeffrey_start', 'jeffrey_duration']
            )
        elif order == ['jeffrey', 'sarah', 'brian']:
            temp_problem.addConstraint(
                lambda j_s, j_d, s_s, s_d: j_s + j_d + travel_times[('Union Square', 'North Beach')] <= s_s,
                ['jeffrey_start', 'jeffrey_duration', 'sarah_start', 'sarah_duration']
            )
            temp_problem.addConstraint(
                lambda s_s, s_d, b_s, b_d: s_s + s_d + travel_times[('North Beach', 'Alamo Square')] <= b_s,
                ['sarah_start', 'sarah_duration', 'brian_start', 'brian_duration']
            )
        elif order == ['jeffrey', 'brian', 'sarah']:
            temp_problem.addConstraint(
                lambda j_s, j_d, b_s, b_d: j_s + j_d + travel_times[('Union Square', 'Alamo Square')] <= b_s,
                ['jeffrey_start', 'jeffrey_duration', 'brian_start', 'brian_duration']
            )
            temp_problem.addConstraint(
                lambda b_s, b_d, s_s, s_d: b_s + b_d + travel_times[('Alamo Square', 'North Beach')] <= s_s,
                ['brian_start', 'brian_duration', 'sarah_start', 'sarah_duration']
            )
        elif order == ['brian', 'sarah', 'jeffrey']:
            temp_problem.addConstraint(
                lambda b_s, b_d, s_s, s_d: b_s + b_d + travel_times[('Alamo Square', 'North Beach')] <= s_s,
                ['brian_start', 'brian_duration', 'sarah_start', 'sarah_duration']
            )
            temp_problem.addConstraint(
                lambda s_s, s_d, j_s, j_d: s_s + s_d + travel_times[('North Beach', 'Union Square')] <= j_s,
                ['sarah_start', 'sarah_duration', 'jeffrey_start', 'jeffrey_duration']
            )
        elif order == ['brian', 'jeffrey', 'sarah']:
            temp_problem.addConstraint(
                lambda b_s, b_d, j_s, j_d: b_s + b_d + travel_times[('Alamo Square', 'Union Square')] <= j_s,
                ['brian_start', 'brian_duration', 'jeffrey_start', 'jeffrey_duration']
            )
            temp_problem.addConstraint(
                lambda j_s, j_d, s_s, s_d: j_s + j_d + travel_times[('Union Square', 'North Beach')] <= s_s,
                ['jeffrey_start', 'jeffrey_duration', 'sarah_start', 'sarah_duration']
            )
        
        # Try to find a solution
        solutions = temp_problem.getSolutions()
        
        if solutions:
            # Find solution with maximum total meeting time
            for solution in solutions:
                total_time = (solution['sarah_duration'] + 
                            solution['jeffrey_duration'] + 
                            solution['brian_duration'])
                
                if total_time > best_total_time:
                    best_total_time = total_time
                    best_solution = {
                        'order': order,
                        'sarah_start': solution['sarah_start'],
                        'sarah_duration': solution['sarah_duration'],
                        'jeffrey_start': solution['jeffrey_start'],
                        'jeffrey_duration': solution['jeffrey_duration'],
                        'brian_start': solution['brian_start'],
                        'brian_duration': solution['brian_duration']
                    }
    
    # Build the itinerary
    itinerary = []
    
    if best_solution:
        order = best_solution['order']
        
        # Add travel from Sunset District to first location
        first_person = order[0]
        if first_person == 'sarah':
            first_location = 'North Beach'
            travel_from_sunset = travel_times[('Sunset District', 'North Beach')]
            first_start = best_solution['sarah_start']
        elif first_person == 'jeffrey':
            first_location = 'Union Square'
            travel_from_sunset = travel_times[('Sunset District', 'Union Square')]
            first_start = best_solution['jeffrey_start']
        else:  # brian
            first_location = 'Alamo Square'
            travel_from_sunset = travel_times[('Sunset District', 'Alamo Square')]
            first_start = best_solution['brian_start']
        
        # Add meetings in order
        for person in order:
            if person == 'sarah':
                itinerary.append({
                    "action": "meet",
                    "location": "North Beach",
                    "person": "Sarah",
                    "start_time": minutes_to_time(best_solution['sarah_start']),
                    "end_time": minutes_to_time(best_solution['sarah_start'] + best_solution['sarah_duration'])
                })
            elif person == 'jeffrey':
                itinerary.append({
                    "action": "meet",
                    "location": "Union Square",
                    "person": "Jeffrey",
                    "start_time": minutes_to_time(best_solution['jeffrey_start']),
                    "end_time": minutes_to_time(best_solution['jeffrey_start'] + best_solution['jeffrey_duration'])
                })
            else:  # brian
                itinerary.append({
                    "action": "meet",
                    "location": "Alamo Square",
                    "person": "Brian",
                    "start_time": minutes_to_time(best_solution['brian_start']),
                    "end_time": minutes_to_time(best_solution['brian_start'] + best_solution['brian_duration'])
                })
    
    # If no solution found with all three, try with two friends
    if not best_solution:
        # Try different combinations of two friends
        friend_combinations = [
            ['sarah', 'jeffrey'],
            ['sarah', 'brian'],
            ['jeffrey', 'brian'],
            ['jeffrey', 'sarah'],
            ['brian', 'sarah'],
            ['brian', 'jeffrey']
        ]
        
        for combo in friend_combinations:
            temp_problem = constraint.Problem()
            
            # Add variables only for the two friends
            if 'sarah' in combo:
                temp_problem.addVariable('sarah_start', sarah_start_range)
                temp_problem.addVariable('sarah_duration', sarah_duration_range)
            if 'jeffrey' in combo:
                temp_problem.addVariable('jeffrey_start', jeffrey_start_range)
                temp_problem.addVariable('jeffrey_duration', jeffrey_duration_range)
            if 'brian' in combo:
                temp_problem.addVariable('brian_start', brian_start_range)
                temp_problem.addVariable('brian_duration', brian_duration_range)
            
            # Availability constraints
            if 'sarah' in combo:
                temp_problem.addConstraint(lambda start, duration: start + duration <= sarah_available_end, ['sarah_start', 'sarah_duration'])
            if 'jeffrey' in combo:
                temp_problem.addConstraint(lambda start, duration: start + duration <= jeffrey_available_end, ['jeffrey_start', 'jeffrey_duration'])
            if 'brian' in combo:
                temp_problem.addConstraint(lambda start, duration: start + duration <= brian_available_end, ['brian_start', 'brian_duration'])
            
            # Travel constraints for the two friends
            if combo == ['sarah', 'jeffrey']:
                temp_problem.addConstraint(
                    lambda s_s, s_d, j_s, j_d: s_s + s_d + travel_times[('North Beach', 'Union Square')] <= j_s,
                    ['sarah_start', 'sarah_duration', 'jeffrey_start', 'jeffrey_duration']
                )
            elif combo == ['jeffrey', 'sarah']:
                temp_problem.addConstraint(
                    lambda j_s, j_d, s_s, s_d: j_s + j_d + travel_times[('Union Square', 'North Beach')] <= s_s,
                    ['jeffrey_start', 'jeffrey_duration', 'sarah_start', 'sarah_duration']
                )
            elif combo == ['sarah', 'brian']:
                temp_problem.addConstraint(
                    lambda s_s, s_d, b_s, b_d: s_s + s_d + travel_times[('North Beach', 'Alamo Square')] <= b_s,
                    ['sarah_start', 'sarah_duration', 'brian_start', 'brian_duration']
                )
            elif combo == ['brian', 'sarah']:
                temp_problem.addConstraint(
                    lambda b_s, b_d, s_s, s_d: b_s + b_d + travel_times[('Alamo Square', 'North Beach')] <= s_s,
                    ['brian_start', 'brian_duration', 'sarah_start', 'sarah_duration']
                )
            elif combo == ['jeffrey', 'brian']:
                temp_problem.addConstraint(
                    lambda j_s, j_d, b_s, b_d: j_s + j_d + travel_times[('Union Square', 'Alamo Square')] <= b_s,
                    ['jeffrey_start', 'jeffrey_duration', 'brian_start', 'brian_duration']
                )
            elif combo == ['brian', 'jeffrey']:
                temp_problem.addConstraint(
                    lambda b_s, b_d, j_s, j_d: b_s + b_d + travel_times[('Alamo Square', 'Union Square')] <= j_s,