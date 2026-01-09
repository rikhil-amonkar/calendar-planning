from constraint import Problem
import json

def main():
    # Travel times in minutes
    travel_times = {
        ('North Beach', 'Mission District'): 18,
        ('North Beach', 'The Castro'): 22,
        ('Mission District', 'North Beach'): 17,
        ('Mission District', 'The Castro'): 7,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Mission District'): 7
    }
    
    # Convert times to minutes since 9:00 (540 minutes)
    james_start = 12 * 60 + 45 - 540  # 12:45 PM
    james_end = 14 * 60 - 540         # 2:00 PM
    robert_start = 12 * 60 + 45 - 540  # 12:45 PM
    robert_end = 15 * 60 + 15 - 540    # 3:15 PM
    
    james_min_duration = 75
    robert_min_duration = 30
    
    problem = Problem()
    
    # Variables: start times and durations for each meeting
    # james_start_time, james_duration, robert_start_time, robert_duration
    # meeting_order: 0 = meet James first, 1 = meet Robert first
    
    # Add variables with reasonable ranges
    problem.addVariable("james_start", range(james_start, james_end - james_min_duration + 1))
    problem.addVariable("james_duration", range(james_min_duration, james_end - james_start + 1))
    problem.addVariable("robert_start", range(robert_start, robert_end - robert_min_duration + 1))
    problem.addVariable("robert_duration", range(robert_min_duration, robert_end - robert_start + 1))
    problem.addVariable("meeting_order", [0, 1])
    
    def meeting_constraints(js, jd, rs, rd, order):
        # Ensure meetings don't exceed available time windows
        if js + jd > james_end or rs + rd > robert_end:
            return False
        
        # Travel constraints based on meeting order
        if order == 0:  # Meet James first, then Robert
            travel_time = travel_times[('Mission District', 'The Castro')]
            if js + jd + travel_time > rs:
                return False
        else:  # Meet Robert first, then James
            travel_time = travel_times[('The Castro', 'Mission District')]
            if rs + rd + travel_time > js:
                return False
        
        return True
    
    problem.addConstraint(meeting_constraints, 
                         ["james_start", "james_duration", "robert_start", "robert_duration", "meeting_order"])
    
    # Objective: maximize total meeting time
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet at least one person
        problem2 = Problem()
        problem2.addVariable("james_start", range(james_start, james_end - james_min_duration + 1))
        problem2.addVariable("james_duration", range(james_min_duration, james_end - james_start + 1))
        
        def james_only_constraint(js, jd):
            return js + jd <= james_end
        
        problem2.addConstraint(james_only_constraint, ["james_start", "james_duration"])
        
        james_solutions = problem2.getSolutions()
        if james_solutions:
            best_solution = max(james_solutions, key=lambda s: s["james_duration"])
            itinerary = [
                {
                    "action": "meet",
                    "location": "Mission District", 
                    "person": "James",
                    "start_time": minutes_to_time(best_solution["james_start"] + 540),
                    "end_time": minutes_to_time(best_solution["james_start"] + best_solution["james_duration"] + 540)
                }
            ]
            print(json.dumps({"itinerary": itinerary}, indent=2))
            return
        
        # Try Robert only
        problem3 = Problem()
        problem3.addVariable("robert_start", range(robert_start, robert_end - robert_min_duration + 1))
        problem3.addVariable("robert_duration", range(robert_min_duration, robert_end - robert_start + 1))
        
        def robert_only_constraint(rs, rd):
            return rs + rd <= robert_end
        
        problem3.addConstraint(robert_only_constraint, ["robert_start", "robert_duration"])
        
        robert_solutions = problem3.getSolutions()
        if robert_solutions:
            best_solution = max(robert_solutions, key=lambda s: s["robert_duration"])
            itinerary = [
                {
                    "action": "meet",
                    "location": "The Castro",
                    "person": "Robert",
                    "start_time": minutes_to_time(best_solution["robert_start"] + 540),
                    "end_time": minutes_to_time(best_solution["robert_start"] + best_solution["robert_duration"] + 540)
                }
            ]
            print(json.dumps({"itinerary": itinerary}, indent=2))
            return
        
        # No meetings possible
        print(json.dumps({"itinerary": []}, indent=2))
        return
    
    # Find solution with maximum total meeting time
    best_solution = max(solutions, key=lambda s: s["james_duration"] + s["robert_duration"])
    
    itinerary = []
    
    if best_solution["meeting_order"] == 0:  # James first, then Robert
        # Add travel from North Beach to Mission District
        travel_start = 9 * 60  # 9:00 AM
        travel_end = travel_start + travel_times[('North Beach', 'Mission District')]
        
        itinerary.append({
            "action": "travel",
            "location": "Mission District",
            "person": "None",
            "start_time": minutes_to_time(travel_start),
            "end_time": minutes_to_time(travel_end)
        })
        
        # James meeting
        james_meeting_start = best_solution["james_start"] + 540
        james_meeting_end = james_meeting_start + best_solution["james_duration"]
        
        itinerary.append({
            "action": "meet",
            "location": "Mission District",
            "person": "James",
            "start_time": minutes_to_time(james_meeting_start),
            "end_time": minutes_to_time(james_meeting_end)
        })
        
        # Travel to Robert
        travel_start = james_meeting_end
        travel_end = travel_start + travel_times[('Mission District', 'The Castro')]
        
        itinerary.append({
            "action": "travel",
            "location": "The Castro",
            "person": "None",
            "start_time": minutes_to_time(travel_start),
            "end_time": minutes_to_time(travel_end)
        })
        
        # Robert meeting
        robert_meeting_start = best_solution["robert_start"] + 540
        robert_meeting_end = robert_meeting_start + best_solution["robert_duration"]
        
        itinerary.append({
            "action": "meet",
            "location": "The Castro",
            "person": "Robert",
            "start_time": minutes_to_time(robert_meeting_start),
            "end_time": minutes_to_time(robert_meeting_end)
        })
        
    else:  # Robert first, then James
        # Add travel from North Beach to The Castro
        travel_start = 9 * 60  # 9:00 AM
        travel_end = travel_start + travel_times[('North Beach', 'The Castro')]
        
        itinerary.append({
            "action": "travel",
            "location": "The Castro",
            "person": "None",
            "start_time": minutes_to_time(travel_start),
            "end_time": minutes_to_time(travel_end)
        })
        
        # Robert meeting
        robert_meeting_start = best_solution["robert_start"] + 540
        robert_meeting_end = robert_meeting_start + best_solution["robert_duration"]
        
        itinerary.append({
            "action": "meet",
            "location": "The Castro",
            "person": "Robert",
            "start_time": minutes_to_time(robert_meeting_start),
            "end_time": minutes_to_time(robert_meeting_end)
        })
        
        # Travel to James
        travel_start = robert_meeting_end
        travel_end = travel_start + travel_times[('The Castro', 'Mission District')]
        
        itinerary.append({
            "action": "travel",
            "location": "Mission District",
            "person": "None",
            "start_time": minutes_to_time(travel_start),
            "end_time": minutes_to_time(travel_end)
        })
        
        # James meeting
        james_meeting_start = best_solution["james_start"] + 540
        james_meeting_end = james_meeting_start + best_solution["james_duration"]
        
        itinerary.append({
            "action": "meet",
            "location": "Mission District",
            "person": "James",
            "start_time": minutes_to_time(james_meeting_start),
            "end_time": minutes_to_time(james_meeting_end)
        })
    
    print(json.dumps({"itinerary": itinerary}, indent=2))

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

if __name__ == "__main__":
    main()