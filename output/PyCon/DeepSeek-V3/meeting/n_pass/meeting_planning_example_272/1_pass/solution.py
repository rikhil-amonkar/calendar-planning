import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes
    travel_times = {
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', 'Nob Hill'): 12,
        ('Mission District', 'Embarcadero'): 19,
        ('Embarcadero', 'Russian Hill'): 8,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Mission District'): 20
    }
    
    # Convert all times to minutes since 9:00 AM
    def time_to_minutes(time_str):
        if ':' in time_str:
            hours, minutes = time_str.split(':')
            am_pm = minutes[-2:]
            minutes = minutes[:-2] if am_pm in ['AM', 'PM'] else minutes
            hours = int(hours)
            minutes = int(minutes)
            if am_pm == 'PM' and hours != 12:
                hours += 12
            elif am_pm == 'AM' and hours == 12:
                hours = 0
            return hours * 60 + minutes
        return int(time_str)
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    # Friend constraints
    friends = {
        'Patricia': {
            'location': 'Nob Hill',
            'available_start': time_to_minutes('18:30'),
            'available_end': time_to_minutes('21:45'),
            'min_duration': 90
        },
        'Ashley': {
            'location': 'Mission District',
            'available_start': time_to_minutes('20:30'),
            'available_end': time_to_minutes('21:15'),
            'min_duration': 45
        },
        'Timothy': {
            'location': 'Embarcadero',
            'available_start': time_to_minutes('9:45'),
            'available_end': time_to_minutes('17:45'),
            'min_duration': 120
        }
    }
    
    start_location = 'Russian Hill'
    start_time = time_to_minutes('9:00')
    
    # Create problem
    problem = constraint.Problem()
    
    # Define variables for meeting start times and durations
    friend_order = ['Timothy', 'Patricia', 'Ashley']
    
    # Variables: start time for each meeting
    for friend in friend_order:
        friend_info = friends[friend]
        problem.addVariable(f'{friend}_start', 
                           range(friend_info['available_start'], 
                                 friend_info['available_end'] - friend_info['min_duration'] + 1))
        problem.addVariable(f'{friend}_duration', 
                           range(friend_info['min_duration'], 
                                 friend_info['available_end'] - friend_info['available_start'] + 1))
    
    # Constraint: meeting must end within available time
    for friend in friend_order:
        friend_info = friends[friend]
        def meeting_within_time(friend_start, friend_duration, f=friend, fi=friend_info):
            return friend_start + friend_duration <= fi['available_end']
        problem.addConstraint(meeting_within_time, [f'{friend}_start', f'{friend}_duration'])
    
    # Constraint: travel time between meetings
    def travel_constraints(timothy_start, timothy_duration, patricia_start, patricia_duration, ashley_start, ashley_duration):
        # Possible orders: T->P->A, T->A->P, P->T->A, P->A->T, A->T->P, A->P->T
        # But we need to check feasibility based on travel times
        
        # Calculate end times
        timothy_end = timothy_start + timothy_duration
        patricia_end = patricia_start + patricia_duration
        ashley_end = ashley_start + ashley_duration
        
        # Check all possible orders
        orders = [
            # T->P->A
            (('Timothy', timothy_start, timothy_end), ('Patricia', patricia_start, patricia_end), ('Ashley', ashley_start, ashley_end)),
            # T->A->P
            (('Timothy', timothy_start, timothy_end), ('Ashley', ashley_start, ashley_end), ('Patricia', patricia_start, patricia_end)),
            # P->T->A
            (('Patricia', patricia_start, patricia_end), ('Timothy', timothy_start, timothy_end), ('Ashley', ashley_start, ashley_end)),
            # P->A->T
            (('Patricia', patricia_start, patricia_end), ('Ashley', ashley_start, ashley_end), ('Timothy', timothy_start, timothy_end)),
            # A->T->P
            (('Ashley', ashley_start, ashley_end), ('Timothy', timothy_start, timothy_end), ('Patricia', patricia_start, patricia_end)),
            # A->P->T
            (('Ashley', ashley_start, ashley_end), ('Patricia', patricia_start, patricia_end), ('Timothy', timothy_start, timothy_end))
        ]
        
        for order in orders:
            feasible = True
            current_time = start_time
            current_loc = start_location
            
            for meeting in order:
                friend_name, m_start, m_end = meeting
                friend_loc = friends[friend_name]['location']
                
                # Travel to meeting
                travel_time = travel_times.get((current_loc, friend_loc), 60)  # Default high if no direct route
                
                # Arrival time at meeting
                arrival_time = current_time + travel_time
                
                # Check if we can make it to the meeting on time
                if arrival_time > m_start:
                    feasible = False
                    break
                
                # Update current time and location
                current_time = m_end
                current_loc = friend_loc
            
            if feasible:
                return True
        
        return False
    
    problem.addConstraint(travel_constraints, 
                         ['Timothy_start', 'Timothy_duration', 
                          'Patricia_start', 'Patricia_duration', 
                          'Ashley_start', 'Ashley_duration'])
    
    # Find solution that maximizes total meeting time
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet at least some friends
        # Try meeting just Timothy and Patricia
        problem_fallback = constraint.Problem()
        problem_fallback.addVariable('Timothy_start', 
                                   range(friends['Timothy']['available_start'], 
                                         friends['Timothy']['available_end'] - friends['Timothy']['min_duration'] + 1))
        problem_fallback.addVariable('Timothy_duration', 
                                   range(friends['Timothy']['min_duration'], 
                                         friends['Timothy']['available_end'] - friends['Timothy']['available_start'] + 1))
        problem_fallback.addVariable('Patricia_start', 
                                   range(friends['Patricia']['available_start'], 
                                         friends['Patricia']['available_end'] - friends['Patricia']['min_duration'] + 1))
        problem_fallback.addVariable('Patricia_duration', 
                                   range(friends['Patricia']['min_duration'], 
                                         friends['Patricia']['available_end'] - friends['Patricia']['available_start'] + 1))
        
        def fallback_constraint(t_start, t_dur, p_start, p_dur):
            t_end = t_start + t_dur
            p_end = p_start + p_dur
            
            # Travel from start to Timothy
            travel1 = travel_times[(start_location, friends['Timothy']['location'])]
            # Travel from Timothy to Patricia
            travel2 = travel_times[(friends['Timothy']['location'], friends['Patricia']['location'])]
            
            # Check if we can make both meetings
            arrival_at_t = start_time + travel1
            if arrival_at_t > t_start:
                return False
                
            arrival_at_p = t_end + travel2
            if arrival_at_p > p_start:
                return False
                
            return True
        
        problem_fallback.addConstraint(fallback_constraint, 
                                      ['Timothy_start', 'Timothy_duration', 'Patricia_start', 'Patricia_duration'])
        
        solutions_fallback = problem_fallback.getSolutions()
        
        if solutions_fallback:
            best_solution = max(solutions_fallback, key=lambda s: s['Timothy_duration'] + s['Patricia_duration'])
            
            # Build itinerary
            itinerary = []
            
            # Meet Timothy
            t_start = best_solution['Timothy_start']
            t_end = t_start + best_solution['Timothy_duration']
            itinerary.append({
                "action": "meet",
                "location": friends['Timothy']['location'],
                "person": "Timothy",
                "start_time": minutes_to_time(t_start),
                "end_time": minutes_to_time(t_end)
            })
            
            # Meet Patricia
            p_start = best_solution['Patricia_start']
            p_end = p_start + best_solution['Patricia_duration']
            itinerary.append({
                "action": "meet",
                "location": friends['Patricia']['location'],
                "person": "Patricia",
                "start_time": minutes_to_time(p_start),
                "end_time": minutes_to_time(p_end)
            })
            
            result = {"itinerary": itinerary}
            print(json.dumps(result, indent=2))
            return
    
    if solutions:
        # Find solution with maximum total meeting time
        best_solution = max(solutions, key=lambda s: s['Timothy_duration'] + s['Patricia_duration'] + s['Ashley_duration'])
        
        # Build itinerary in chronological order
        meetings = [
            ("Timothy", best_solution['Timothy_start'], best_solution['Timothy_start'] + best_solution['Timothy_duration']),
            ("Patricia", best_solution['Patricia_start'], best_solution['Patricia_start'] + best_solution['Patricia_duration']),
            ("Ashley", best_solution['Ashley_start'], best_solution['Ashley_start'] + best_solution['Ashley_duration'])
        ]
        
        # Sort by start time
        meetings.sort(key=lambda x: x[1])
        
        itinerary = []
        for meeting in meetings:
            friend, start, end = meeting
            itinerary.append({
                "action": "meet",
                "location": friends[friend]['location'],
                "person": friend,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # No feasible solution found
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()