import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes between locations
    travel_times = {
        ('Golden Gate Park', 'Alamo Square'): 10,
        ('Golden Gate Park', 'Presidio'): 11,
        ('Golden Gate Park', 'Russian Hill'): 19,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Presidio'): 18,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Presidio', 'Golden Gate Park'): 12,
        ('Presidio', 'Alamo Square'): 18,
        ('Presidio', 'Russian Hill'): 14,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Presidio'): 14
    }
    
    # Convert all times to minutes since 9:00 AM
    start_time_base = datetime.strptime('9:00', '%H:%M')
    
    # Friend constraints in minutes since 9:00 AM
    timothy_start = (datetime.strptime('12:00', '%H:%M') - start_time_base).total_seconds() / 60
    timothy_end = (datetime.strptime('16:15', '%H:%M') - start_time_base).total_seconds() / 60
    timothy_min = 105
    
    mark_start = (datetime.strptime('18:45', '%H:%M') - start_time_base).total_seconds() / 60
    mark_end = (datetime.strptime('21:00', '%H:%M') - start_time_base).total_seconds() / 60
    mark_min = 60
    
    joseph_start = (datetime.strptime('16:45', '%H:%M') - start_time_base).total_seconds() / 60
    joseph_end = (datetime.strptime('21:30', '%H:%M') - start_time_base).total_seconds() / 60
    joseph_min = 60
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start times for each meeting (in minutes since 9:00 AM)
    # We'll use discrete time intervals of 15 minutes for efficiency
    time_step = 15
    max_time = (datetime.strptime('21:30', '%H:%M') - start_time_base).total_seconds() / 60
    
    # Generate possible start times for each meeting
    timothy_times = [t for t in range(int(timothy_start), int(timothy_end - timothy_min + 1), time_step)]
    mark_times = [t for t in range(int(mark_start), int(mark_end - mark_min + 1), time_step)]
    joseph_times = [t for t in range(int(joseph_start), int(joseph_end - joseph_min + 1), time_step)]
    
    # Add variables
    problem.addVariable('timothy_start', timothy_times)
    problem.addVariable('mark_start', mark_times)
    problem.addVariable('joseph_start', joseph_times)
    
    # Calculate end times
    def get_end_time(start, duration):
        return start + duration
    
    # Constraint: meetings must not overlap and account for travel time
    def no_overlap(timothy_s, mark_s, joseph_s):
        timothy_e = get_end_time(timothy_s, timothy_min)
        mark_e = get_end_time(mark_s, mark_min)
        joseph_e = get_end_time(joseph_s, joseph_min)
        
        # Check all possible orders and ensure travel time is accounted for
        orders = [
            # Timothy -> Mark -> Joseph
            (timothy_e + travel_times[('Alamo Square', 'Presidio')] <= mark_s and 
             mark_e + travel_times[('Presidio', 'Russian Hill')] <= joseph_s),
            
            # Timothy -> Joseph -> Mark
            (timothy_e + travel_times[('Alamo Square', 'Russian Hill')] <= joseph_s and 
             joseph_e + travel_times[('Russian Hill', 'Presidio')] <= mark_s),
            
            # Mark -> Timothy -> Joseph
            (mark_e + travel_times[('Presidio', 'Alamo Square')] <= timothy_s and 
             timothy_e + travel_times[('Alamo Square', 'Russian Hill')] <= joseph_s),
            
            # Mark -> Joseph -> Timothy
            (mark_e + travel_times[('Presidio', 'Russian Hill')] <= joseph_s and 
             joseph_e + travel_times[('Russian Hill', 'Alamo Square')] <= timothy_s),
            
            # Joseph -> Timothy -> Mark
            (joseph_e + travel_times[('Russian Hill', 'Alamo Square')] <= timothy_s and 
             timothy_e + travel_times[('Alamo Square', 'Presidio')] <= mark_s),
            
            # Joseph -> Mark -> Timothy
            (joseph_e + travel_times[('Russian Hill', 'Presidio')] <= mark_s and 
             mark_e + travel_times[('Presidio', 'Alamo Square')] <= timothy_s)
        ]
        
        return any(orders)
    
    problem.addConstraint(no_overlap, ['timothy_start', 'mark_start', 'joseph_start'])
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many friends as possible
        best_solution = None
        max_meetings = 0
        
        # Try all combinations of 2 meetings
        for combo in [['timothy', 'mark'], ['timothy', 'joseph'], ['mark', 'joseph']]:
            if 'timothy' in combo and 'mark' in combo:
                sub_problem = constraint.Problem()
                sub_problem.addVariable('timothy_start', timothy_times)
                sub_problem.addVariable('mark_start', mark_times)
                
                def two_meeting_constraint(ts, ms):
                    te = get_end_time(ts, timothy_min)
                    me = get_end_time(ms, mark_min)
                    return (te + travel_times[('Alamo Square', 'Presidio')] <= ms or 
                            me + travel_times[('Presidio', 'Alamo Square')] <= ts)
                
                sub_problem.addConstraint(two_meeting_constraint, ['timothy_start', 'mark_start'])
                sub_solutions = sub_problem.getSolutions()
                if sub_solutions and len(combo) > max_meetings:
                    max_meetings = len(combo)
                    best_solution = {'timothy_start': sub_solutions[0]['timothy_start'], 
                                   'mark_start': sub_solutions[0]['mark_start']}
            
            elif 'timothy' in combo and 'joseph' in combo:
                sub_problem = constraint.Problem()
                sub_problem.addVariable('timothy_start', timothy_times)
                sub_problem.addVariable('joseph_start', joseph_times)
                
                def two_meeting_constraint(ts, js):
                    te = get_end_time(ts, timothy_min)
                    je = get_end_time(js, joseph_min)
                    return (te + travel_times[('Alamo Square', 'Russian Hill')] <= js or 
                            je + travel_times[('Russian Hill', 'Alamo Square')] <= ts)
                
                sub_problem.addConstraint(two_meeting_constraint, ['timothy_start', 'joseph_start'])
                sub_solutions = sub_problem.getSolutions()
                if sub_solutions and len(combo) > max_meetings:
                    max_meetings = len(combo)
                    best_solution = {'timothy_start': sub_solutions[0]['timothy_start'], 
                                   'joseph_start': sub_solutions[0]['joseph_start']}
            
            elif 'mark' in combo and 'joseph' in combo:
                sub_problem = constraint.Problem()
                sub_problem.addVariable('mark_start', mark_times)
                sub_problem.addVariable('joseph_start', joseph_times)
                
                def two_meeting_constraint(ms, js):
                    me = get_end_time(ms, mark_min)
                    je = get_end_time(js, joseph_min)
                    return (me + travel_times[('Presidio', 'Russian Hill')] <= js or 
                            je + travel_times[('Russian Hill', 'Presidio')] <= ms)
                
                sub_problem.addConstraint(two_meeting_constraint, ['mark_start', 'joseph_start'])
                sub_solutions = sub_problem.getSolutions()
                if sub_solutions and len(combo) > max_meetings:
                    max_meetings = len(combo)
                    best_solution = {'mark_start': sub_solutions[0]['mark_start'], 
                                   'joseph_start': sub_solutions[0]['joseph_start']}
        
        if best_solution:
            solution = best_solution
        else:
            # If no two meetings work, pick the longest single meeting
            longest_meeting = max([(timothy_min, 'timothy', timothy_times[0]),
                                 (mark_min, 'mark', mark_times[0]),
                                 (joseph_min, 'joseph', joseph_times[0])], 
                                key=lambda x: x[0])
            solution = {f'{longest_meeting[1]}_start': longest_meeting[2]}
    else:
        solution = solutions[0]
    
    # Build itinerary
    itinerary = []
    
    # Convert minutes back to time strings
    def minutes_to_time(minutes):
        time_obj = start_time_base + timedelta(minutes=minutes)
        return time_obj.strftime('%H:%M').lstrip('0')
    
    # Add travel from Golden Gate Park to first meeting
    meetings = []
    if 'timothy_start' in solution:
        meetings.append(('timothy', 'Alamo Square', 'Timothy', 
                        solution['timothy_start'], timothy_min))
    if 'mark_start' in solution:
        meetings.append(('mark', 'Presidio', 'Mark', 
                        solution['mark_start'], mark_min))
    if 'joseph_start' in solution:
        meetings.append(('joseph', 'Russian Hill', 'Joseph', 
                        solution['joseph_start'], joseph_min))
    
    # Sort meetings by start time
    meetings.sort(key=lambda x: x[3])
    
    # Add travel from Golden Gate Park to first meeting
    if meetings:
        first_meeting = meetings[0]
        travel_time = travel_times[('Golden Gate Park', first_meeting[1])]
        itinerary.append({
            "action": "travel",
            "location": first_meeting[1],
            "person": "",
            "start_time": minutes_to_time(0),
            "end_time": minutes_to_time(travel_time)
        })
    
    # Add meetings
    for i, (_, location, person, start, duration) in enumerate(meetings):
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(start + duration)
        })
        
        # Add travel to next meeting if there is one
        if i < len(meetings) - 1:
            next_meeting = meetings[i + 1]
            travel_duration = travel_times[(location, next_meeting[1])]
            itinerary.append({
                "action": "travel",
                "location": next_meeting[1],
                "person": "",
                "start_time": minutes_to_time(start + duration),
                "end_time": minutes_to_time(start + duration + travel_duration)
            })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()