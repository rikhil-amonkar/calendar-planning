import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times dictionary (in minutes)
    travel_times = {
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'Financial District'): 5,
        ('Embarcadero', 'Pacific Heights'): 11,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Bayview'): 21,
        ('Richmond District', 'Embarcadero'): 19,
        ('Richmond District', 'Union Square'): 21,
        ('Richmond District', 'Financial District'): 22,
        ('Richmond District', 'Pacific Heights'): 10,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Bayview'): 26,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Richmond District'): 20,
        ('Union Square', 'Financial District'): 9,
        ('Union Square', 'Pacific Heights'): 15,
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Bayview'): 15,
        ('Financial District', 'Embarcadero'): 4,
        ('Financial District', 'Richmond District'): 21,
        ('Financial District', 'Union Square'): 9,
        ('Financial District', 'Pacific Heights'): 13,
        ('Financial District', 'Nob Hill'): 8,
        ('Financial District', 'Bayview'): 19,
        ('Pacific Heights', 'Embarcadero'): 10,
        ('Pacific Heights', 'Richmond District'): 12,
        ('Pacific Heights', 'Union Square'): 12,
        ('Pacific Heights', 'Financial District'): 13,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Bayview'): 22,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'Financial District'): 9,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Bayview'): 19,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Union Square'): 17,
        ('Bayview', 'Financial District'): 19,
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Nob Hill'): 20
    }

    # Friend constraints
    friends = {
        'Kenneth': {
            'location': 'Richmond District',
            'available_start': datetime.strptime('21:15', '%H:%M'),  # 9:15 PM
            'available_end': datetime.strptime('22:00', '%H:%M'),    # 10:00 PM
            'min_duration': 30  # minutes
        },
        'Lisa': {
            'location': 'Union Square',
            'available_start': datetime.strptime('9:00', '%H:%M'),
            'available_end': datetime.strptime('16:30', '%H:%M'),
            'min_duration': 45
        },
        'Joshua': {
            'location': 'Financial District',
            'available_start': datetime.strptime('12:00', '%H:%M'),
            'available_end': datetime.strptime('15:15', '%H:%M'),
            'min_duration': 15
        },
        'Nancy': {
            'location': 'Pacific Heights',
            'available_start': datetime.strptime('8:00', '%H:%M'),
            'available_end': datetime.strptime('11:30', '%H:%M'),
            'min_duration': 90
        },
        'Andrew': {
            'location': 'Nob Hill',
            'available_start': datetime.strptime('11:30', '%H:%M'),
            'available_end': datetime.strptime('20:15', '%H:%M'),
            'min_duration': 60
        },
        'John': {
            'location': 'Bayview',
            'available_start': datetime.strptime('16:45', '%H:%M'),
            'available_end': datetime.strptime('21:30', '%H:%M'),
            'min_duration': 75
        }
    }

    # Convert times to minutes since 9:00 AM for easier computation
    base_time = datetime.strptime('9:00', '%H:%M')
    
    def time_to_minutes(t):
        return int((t - base_time).total_seconds() / 60)
    
    def minutes_to_time_str(minutes):
        time_obj = base_time + timedelta(minutes=minutes)
        return time_obj.strftime('%H:%M').lstrip('0') if time_obj.strftime('%H:%M').startswith('0') else time_obj.strftime('%H:%M')

    # Create problem
    problem = constraint.Problem()
    
    # Define variables for each friend: start time and duration
    friend_names = list(friends.keys())
    
    for friend in friend_names:
        info = friends[friend]
        available_start_min = time_to_minutes(info['available_start'])
        available_end_min = time_to_minutes(info['available_end'])
        min_duration = info['min_duration']
        
        # Start time must be within availability window
        problem.addVariable(f"{friend}_start", range(available_start_min, available_end_min - min_duration + 1))
        
        # Duration must be at least the minimum
        problem.addVariable(f"{friend}_duration", range(min_duration, available_end_min - available_start_min + 1))
        
        # End time constraint
        def end_time_constraint(start, duration, friend_name=friend):
            end = start + duration
            return end <= time_to_minutes(friends[friend_name]['available_end'])
        
        problem.addConstraint(end_time_constraint, [f"{friend}_start", f"{friend}_duration"])

    # Define order of visits (simplified approach - visit each friend once)
    # We'll try to maximize the number of friends we can meet
    
    # Add travel time constraints between consecutive meetings
    def travel_constraint(f1_start, f1_duration, f2_start, f1_name, f2_name):
        if f1_name == f2_name:
            return True
            
        f1_location = friends[f1_name]['location']
        f2_location = friends[f2_name]['location']
        
        if f1_location == f2_location:
            travel_time = 0
        else:
            travel_time = travel_times.get((f1_location, f2_location), 999)
        
        f1_end = f1_start + f1_duration
        return f1_end + travel_time <= f2_start
    
    # Try all possible orders and find feasible ones
    def find_feasible_schedules():
        feasible_schedules = []
        
        # Generate all permutations of friends
        from itertools import permutations
        
        for order in permutations(friend_names):
            # Create a subproblem for this order
            subproblem = constraint.Problem()
            
            # Add variables for this order
            for friend in order:
                info = friends[friend]
                available_start_min = time_to_minutes(info['available_start'])
                available_end_min = time_to_minutes(info['available_end'])
                min_duration = info['min_duration']
                
                subproblem.addVariable(f"{friend}_start", 
                                    range(available_start_min, available_end_min - min_duration + 1))
                subproblem.addVariable(f"{friend}_duration", 
                                    range(min_duration, available_end_min - available_start_min + 1))
                
                def end_time_constraint_local(start, duration, f=friend):
                    end = start + duration
                    return end <= time_to_minutes(friends[f]['available_end'])
                
                subproblem.addConstraint(end_time_constraint_local, [f"{friend}_start", f"{friend}_duration"])
            
            # Add travel constraints between consecutive friends in this order
            for i in range(len(order) - 1):
                f1, f2 = order[i], order[i+1]
                f1_loc = friends[f1]['location']
                f2_loc = friends[f2]['location']
                travel_time = travel_times.get((f1_loc, f2_loc), 999)
                
                def travel_constraint_local(start1, dur1, start2, f1=f1, f2=f2, tt=travel_time):
                    end1 = start1 + dur1
                    return end1 + tt <= start2
                
                subproblem.addConstraint(travel_constraint_local, 
                                       [f"{f1}_start", f"{f1}_duration", f"{f2}_start"])
            
            # Find solutions
            solutions = subproblem.getSolutions()
            
            for sol in solutions:
                # Calculate total time spent with friends
                total_time = sum(sol[f"{friend}_duration"] for friend in order)
                feasible_schedules.append((order, sol, total_time, len(order)))
        
        return feasible_schedules
    
    # Find all feasible schedules
    all_schedules = find_feasible_schedules()
    
    if not all_schedules:
        # Fallback: try to find schedule with maximum number of friends
        # Even if travel times don't perfectly align
        best_schedule = None
        max_friends = 0
        
        for friend_count in range(len(friend_names), 0, -1):
            for order in permutations(friend_names, friend_count):
                # Simple check: can we meet these friends in this order?
                current_time = 0  # Start at 9:00 AM
                feasible = True
                schedule = []
                
                for friend in order:
                    info = friends[friend]
                    available_start = max(time_to_minutes(info['available_start']), current_time)
                    available_end = time_to_minutes(info['available_end'])
                    
                    if available_start + info['min_duration'] > available_end:
                        feasible = False
                        break
                    
                    # Schedule meeting
                    start_time = available_start
                    duration = info['min_duration']
                    end_time = start_time + duration
                    
                    schedule.append({
                        'friend': friend,
                        'start': start_time,
                        'duration': duration,
                        'end': end_time
                    })
                    
                    # Update current time for travel to next location
                    if friend != order[-1]:
                        next_friend = order[order.index(friend) + 1]
                        current_location = info['location']
                        next_location = friends[next_friend]['location']
                        travel_time = travel_times.get((current_location, next_location), 999)
                        current_time = end_time + travel_time
                
                if feasible and len(order) >= max_friends:
                    max_friends = len(order)
                    best_schedule = (order, schedule)
                    break
            
            if best_schedule:
                break
        
        if best_schedule:
            order, schedule = best_schedule
            result_schedule = []
            
            for meeting in schedule:
                result_schedule.append({
                    'action': 'meet',
                    'location': friends[meeting['friend']]['location'],
                    'person': meeting['friend'],
                    'start_time': minutes_to_time_str(meeting['start']),
                    'end_time': minutes_to_time_str(meeting['end'])
                })
            
            output = {'itinerary': result_schedule}
            print(json.dumps(output, indent=2))
            return
    
    if all_schedules:
        # Find schedule with maximum number of friends met
        all_schedules.sort(key=lambda x: (x[3], x[2]), reverse=True)
        best_order, best_solution, total_time, friend_count = all_schedules[0]
        
        # Build itinerary
        itinerary = []
        for friend in best_order:
            start_time = best_solution[f"{friend}_start"]
            duration = best_solution[f"{friend}_duration"]
            end_time = start_time + duration
            
            itinerary.append({
                'action': 'meet',
                'location': friends[friend]['location'],
                'person': friend,
                'start_time': minutes_to_time_str(start_time),
                'end_time': minutes_to_time_str(end_time)
            })
        
        output = {'itinerary': itinerary}
        print(json.dumps(output, indent=2))
    else:
        # No feasible schedule found, try a simple greedy approach
        current_location = 'Embarcadero'
        current_time = 0  # 9:00 AM
        visited_friends = set()
        itinerary = []
        
        while True:
            # Find next feasible friend to visit
            next_friend = None
            earliest_start = float('inf')
            
            for friend in friend_names:
                if friend in visited_friends:
                    continue
                
                info = friends[friend]
                travel_time = travel_times.get((current_location, info['location']), 999)
                arrival_time = current_time + travel_time
                available_start = time_to_minutes(info['available_start'])
                available_end = time_to_minutes(info['available_end'])
                
                # Earliest we can start meeting this friend
                meeting_start = max(arrival_time, available_start)
                meeting_end = meeting_start + info['min_duration']
                
                if meeting_end <= available_end and meeting_start < earliest_start:
                    next_friend = friend
                    earliest_start = meeting_start
            
            if next_friend is None:
                break
            
            # Schedule meeting with next friend
            info = friends[next_friend]
            travel_time = travel_times.get((current_location, info['location']), 999)
            arrival_time = current_time + travel_time
            available_start = time_to_minutes(info['available_start'])
            available_end = time_to_minutes(info['available_end'])
            
            meeting_start = max(arrival_time, available_start)
            meeting_end = meeting_start + info['min_duration']
            
            itinerary.append({
                'action': 'meet',
                'location': info['location'],
                'person': next_friend,
                'start_time': minutes_to_time_str(meeting_start),
                'end_time': minutes_to_time_str(meeting_end)
            })
            
            visited_friends.add(next_friend)
            current_location = info['location']
            current_time = meeting_end
        
        output = {'itinerary': itinerary}
        print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()