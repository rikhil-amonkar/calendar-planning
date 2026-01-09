import constraint
from datetime import datetime, timedelta
import json

def main():
    # Travel times in minutes
    travel_times = {
        ('The Castro', 'Mission District'): 7,
        ('The Castro', 'Financial District'): 20,
        ('Mission District', 'The Castro'): 7,
        ('Mission District', 'Financial District'): 17,
        ('Financial District', 'The Castro'): 23,
        ('Financial District', 'Mission District'): 17
    }
    
    # Convert times to minutes since 9:00 AM
    start_of_day = datetime.strptime('9:00', '%H:%M')
    
    # Laura's availability: 12:15 PM to 7:45 PM
    laura_start = (datetime.strptime('12:15', '%H:%M') - start_of_day).total_seconds() / 60
    laura_end = (datetime.strptime('19:45', '%H:%M') - start_of_day).total_seconds() / 60
    
    # Anthony's availability: 12:30 PM to 2:45 PM  
    anthony_start = (datetime.strptime('12:30', '%H:%M') - start_of_day).total_seconds() / 60
    anthony_end = (datetime.strptime('14:45', '%H:%M') - start_of_day).total_seconds() / 60
    
    # Meeting duration requirements
    laura_min_duration = 75
    anthony_min_duration = 30
    
    # Travel times
    castro_to_mission = 7
    castro_to_financial = 20
    mission_to_financial = 17
    financial_to_mission = 17
    
    problem = constraint.Problem()
    
    # Variables: start times and durations for each meeting
    # We'll plan the order: either meet Laura first then Anthony, or Anthony first then Laura
    
    # Option 1: Laura first, then Anthony
    problem.addVariable('laura_start_1', range(int(laura_start), int(laura_end - laura_min_duration) + 1))
    problem.addVariable('laura_duration_1', [laura_min_duration])
    problem.addVariable('anthony_start_1', range(int(anthony_start), int(anthony_end - anthony_min_duration) + 1))
    problem.addVariable('anthony_duration_1', [anthony_min_duration])
    
    # Option 2: Anthony first, then Laura  
    problem.addVariable('anthony_start_2', range(int(anthony_start), int(anthony_end - anthony_min_duration) + 1))
    problem.addVariable('anthony_duration_2', [anthony_min_duration])
    problem.addVariable('laura_start_2', range(int(laura_start), int(laura_end - laura_min_duration) + 1))
    problem.addVariable('laura_duration_2', [laura_min_duration])
    
    # Constraints for Option 1: Laura first, then Anthony
    def constraint_laura_first(laura_s, laura_d, anthony_s, anthony_d):
        # Laura meeting ends at Mission District
        laura_end = laura_s + laura_d
        
        # Travel from Mission to Financial District
        travel_time = mission_to_financial
        
        # Anthony meeting must start after travel time
        if anthony_s >= laura_end + travel_time:
            return True
        return False
    
    # Constraints for Option 2: Anthony first, then Laura
    def constraint_anthony_first(anthony_s, anthony_d, laura_s, laura_d):
        # Anthony meeting ends at Financial District
        anthony_end = anthony_s + anthony_d
        
        # Travel from Financial to Mission District
        travel_time = financial_to_mission
        
        # Laura meeting must start after travel time
        if laura_s >= anthony_end + travel_time:
            return True
        return False
    
    problem.addConstraint(constraint_laura_first, 
                         ['laura_start_1', 'laura_duration_1', 'anthony_start_1', 'anthony_duration_1'])
    
    problem.addConstraint(constraint_anthony_first,
                         ['anthony_start_2', 'anthony_duration_2', 'laura_start_2', 'laura_duration_2'])
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # Try single meetings if both together not possible
        single_meeting_solutions = []
        
        # Just meet Laura
        if laura_end - laura_start >= laura_min_duration:
            single_meeting_solutions.append({
                'type': 'laura_only',
                'laura_start': laura_start,
                'laura_duration': laura_min_duration
            })
        
        # Just meet Anthony  
        if anthony_end - anthony_start >= anthony_min_duration:
            single_meeting_solutions.append({
                'type': 'anthony_only', 
                'anthony_start': anthony_start,
                'anthony_duration': anthony_min_duration
            })
        
        if single_meeting_solutions:
            # Pick the solution that meets someone
            best_solution = single_meeting_solutions[0]
        else:
            # No meetings possible
            best_solution = None
    else:
        # Find the solution that maximizes total meeting time
        best_solution = None
        max_total_time = -1
        
        for sol in solutions:
            if 'laura_start_1' in sol:
                total_time = sol['laura_duration_1'] + sol['anthony_duration_1']
                if total_time > max_total_time:
                    max_total_time = total_time
                    best_solution = {'type': 'both_laura_first', **sol}
            else:
                total_time = sol['laura_duration_2'] + sol['anthony_duration_2'] 
                if total_time > max_total_time:
                    max_total_time = total_time
                    best_solution = {'type': 'both_anthony_first', **sol}
    
    # Build itinerary
    itinerary = []
    
    if best_solution:
        if best_solution['type'] == 'both_laura_first':
            # Start at Castro at 9:00, travel to Mission to meet Laura
            travel_start = start_of_day
            travel_end = start_of_day + timedelta(minutes=castro_to_mission)
            
            # Laura meeting
            laura_meet_start = start_of_day + timedelta(minutes=best_solution['laura_start_1'])
            laura_meet_end = laura_meet_start + timedelta(minutes=best_solution['laura_duration_1'])
            
            # Travel to Financial District
            travel_start_2 = laura_meet_end
            travel_end_2 = travel_start_2 + timedelta(minutes=mission_to_financial)
            
            # Anthony meeting
            anthony_meet_start = start_of_day + timedelta(minutes=best_solution['anthony_start_1'])
            anthony_meet_end = anthony_meet_start + timedelta(minutes=best_solution['anthony_duration_1'])
            
            itinerary = [
                {"action": "travel", "location": "Mission District", "person": "", 
                 "start_time": travel_start.strftime('%H:%M'), "end_time": travel_end.strftime('%H:%M')},
                {"action": "meet", "location": "Mission District", "person": "Laura", 
                 "start_time": laura_meet_start.strftime('%H:%M'), "end_time": laura_meet_end.strftime('%H:%M')},
                {"action": "travel", "location": "Financial District", "person": "", 
                 "start_time": travel_start_2.strftime('%H:%M'), "end_time": travel_end_2.strftime('%H:%M')},
                {"action": "meet", "location": "Financial District", "person": "Anthony", 
                 "start_time": anthony_meet_start.strftime('%H:%M'), "end_time": anthony_meet_end.strftime('%H:%M')}
            ]
            
        elif best_solution['type'] == 'both_anthony_first':
            # Start at Castro at 9:00, travel to Financial to meet Anthony
            travel_start = start_of_day
            travel_end = start_of_day + timedelta(minutes=castro_to_financial)
            
            # Anthony meeting
            anthony_meet_start = start_of_day + timedelta(minutes=best_solution['anthony_start_2'])
            anthony_meet_end = anthony_meet_start + timedelta(minutes=best_solution['anthony_duration_2'])
            
            # Travel to Mission District
            travel_start_2 = anthony_meet_end
            travel_end_2 = travel_start_2 + timedelta(minutes=financial_to_mission)
            
            # Laura meeting
            laura_meet_start = start_of_day + timedelta(minutes=best_solution['laura_start_2'])
            laura_meet_end = laura_meet_start + timedelta(minutes=best_solution['laura_duration_2'])
            
            itinerary = [
                {"action": "travel", "location": "Financial District", "person": "", 
                 "start_time": travel_start.strftime('%H:%M'), "end_time": travel_end.strftime('%H:%M')},
                {"action": "meet", "location": "Financial District", "person": "Anthony", 
                 "start_time": anthony_meet_start.strftime('%H:%M'), "end_time": anthony_meet_end.strftime('%H:%M')},
                {"action": "travel", "location": "Mission District", "person": "", 
                 "start_time": travel_start_2.strftime('%H:%M'), "end_time": travel_end_2.strftime('%H:%M')},
                {"action": "meet", "location": "Mission District", "person": "Laura", 
                 "start_time": laura_meet_start.strftime('%H:%M'), "end_time": laura_meet_end.strftime('%H:%M')}
            ]
            
        elif best_solution['type'] == 'laura_only':
            # Start at Castro at 9:00, travel to Mission to meet Laura
            travel_start = start_of_day
            travel_end = start_of_day + timedelta(minutes=castro_to_mission)
            
            # Laura meeting
            laura_meet_start = start_of_day + timedelta(minutes=best_solution['laura_start'])
            laura_meet_end = laura_meet_start + timedelta(minutes=best_solution['laura_duration'])
            
            itinerary = [
                {"action": "travel", "location": "Mission District", "person": "", 
                 "start_time": travel_start.strftime('%H:%M'), "end_time": travel_end.strftime('%H:%M')},
                {"action": "meet", "location": "Mission District", "person": "Laura", 
                 "start_time": laura_meet_start.strftime('%H:%M'), "end_time": laura_meet_end.strftime('%H:%M')}
            ]
            
        elif best_solution['type'] == 'anthony_only':
            # Start at Castro at 9:00, travel to Financial to meet Anthony
            travel_start = start_of_day
            travel_end = start_of_day + timedelta(minutes=castro_to_financial)
            
            # Anthony meeting
            anthony_meet_start = start_of_day + timedelta(minutes=best_solution['anthony_start'])
            anthony_meet_end = anthony_meet_start + timedelta(minutes=best_solution['anthony_duration'])
            
            itinerary = [
                {"action": "travel", "location": "Financial District", "person": "", 
                 "start_time": travel_start.strftime('%H:%M'), "end_time": travel_end.strftime('%H:%M')},
                {"action": "meet", "location": "Financial District", "person": "Anthony", 
                 "start_time": anthony_meet_start.strftime('%H:%M'), "end_time": anthony_meet_end.strftime('%H:%M')}
            ]
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()