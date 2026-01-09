import constraint
import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    if isinstance(time_str, str):
        dt = datetime.strptime(time_str, "%H:%M")
    else:
        dt = time_str
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Travel times in minutes (symmetric matrix)
    travel_times = {
        "The Castro": {
            "Bayview": 19, "Pacific Heights": 16, "Alamo Square": 8,
            "Fisherman's Wharf": 24, "Golden Gate Park": 11
        },
        "Bayview": {
            "The Castro": 20, "Pacific Heights": 23, "Alamo Square": 16,
            "Fisherman's Wharf": 25, "Golden Gate Park": 22
        },
        "Pacific Heights": {
            "The Castro": 16, "Bayview": 22, "Alamo Square": 10,
            "Fisherman's Wharf": 13, "Golden Gate Park": 15
        },
        "Alamo Square": {
            "The Castro": 8, "Bayview": 16, "Pacific Heights": 10,
            "Fisherman's Wharf": 19, "Golden Gate Park": 9
        },
        "Fisherman's Wharf": {
            "The Castro": 26, "Bayview": 26, "Pacific Heights": 12,
            "Alamo Square": 20, "Golden Gate Park": 25
        },
        "Golden Gate Park": {
            "The Castro": 13, "Bayview": 23, "Pacific Heights": 16,
            "Alamo Square": 10, "Fisherman's Wharf": 24
        }
    }
    
    # Person constraints
    people = {
        "Rebecca": {
            "location": "Bayview",
            "available_start": "9:00",
            "available_end": "12:45",
            "min_duration": 90
        },
        "Amanda": {
            "location": "Pacific Heights", 
            "available_start": "18:30",
            "available_end": "21:45",
            "min_duration": 90
        },
        "James": {
            "location": "Alamo Square",
            "available_start": "9:45", 
            "available_end": "21:15",
            "min_duration": 90
        },
        "Sarah": {
            "location": "Fisherman's Wharf",
            "available_start": "8:00",
            "available_end": "21:30", 
            "min_duration": 90
        },
        "Melissa": {
            "location": "Golden Gate Park",
            "available_start": "9:00",
            "available_end": "18:45",
            "min_duration": 90
        }
    }
    
    # Convert all times to minutes
    start_time = time_to_minutes("9:00")  # Start at The Castro
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start time for each meeting (in minutes since midnight)
    person_names = list(people.keys())
    
    for person in person_names:
        info = people[person]
        available_start = time_to_minutes(info["available_start"])
        available_end = time_to_minutes(info["available_end"])
        min_duration = info["min_duration"]
        
        # Meeting must start within available window and end before available_end
        problem.addVariable(f"{person}_start", range(available_start, available_end - min_duration + 1))
        problem.addVariable(f"{person}_duration", [min_duration])  # Fixed minimum duration
    
    # Constraints: travel time between consecutive meetings
    def travel_constraint(*meeting_times):
        # Create list of meetings with their times and locations
        meetings = []
        for i, person in enumerate(person_names):
            start = meeting_times[i]
            duration = people[person]["min_duration"]
            location = people[person]["location"]
            meetings.append({
                "person": person,
                "start": start,
                "end": start + duration,
                "location": location
            })
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x["start"])
        
        # Check travel times between consecutive meetings
        current_location = "The Castro"
        current_time = start_time
        
        for meeting in meetings:
            # Check if we can travel to this meeting
            travel_time = travel_times[current_location][meeting["location"]]
            
            # We must arrive before meeting starts
            if current_time + travel_time > meeting["start"]:
                return False
            
            # Update current location and time
            current_location = meeting["location"]
            current_time = meeting["end"]
        
        return True
    
    # Add the travel constraint
    problem.addConstraint(travel_constraint, [f"{person}_start" for person in person_names])
    
    # Objective: maximize number of meetings (all meetings have same duration, so earlier end time is better)
    def objective_function(*meeting_times):
        # Return negative of latest end time (so earlier times are better)
        latest_end = 0
        for i, person in enumerate(person_names):
            start = meeting_times[i]
            duration = people[person]["min_duration"]
            latest_end = max(latest_end, start + duration)
        return -latest_end  # Negative because constraint library maximizes
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to schedule as many meetings as possible
        best_solution = None
        best_meetings = 0
        
        # Try all subsets of meetings
        from itertools import combinations
        
        for meeting_count in range(len(person_names), 0, -1):
            for meeting_subset in combinations(person_names, meeting_count):
                sub_problem = constraint.Problem()
                
                for person in meeting_subset:
                    info = people[person]
                    available_start = time_to_minutes(info["available_start"])
                    available_end = time_to_minutes(info["available_end"])
                    min_duration = info["min_duration"]
                    
                    sub_problem.addVariable(f"{person}_start", 
                                          range(available_start, available_end - min_duration + 1))
                    sub_problem.addVariable(f"{person}_duration", [min_duration])
                
                def sub_travel_constraint(*meeting_times):
                    meetings = []
                    for i, person in enumerate(meeting_subset):
                        start = meeting_times[i]
                        duration = people[person]["min_duration"]
                        location = people[person]["location"]
                        meetings.append({
                            "person": person,
                            "start": start,
                            "end": start + duration,
                            "location": location
                        })
                    
                    meetings.sort(key=lambda x: x["start"])
                    current_location = "The Castro"
                    current_time = start_time
                    
                    for meeting in meetings:
                        travel_time = travel_times[current_location][meeting["location"]]
                        if current_time + travel_time > meeting["start"]:
                            return False
                        current_location = meeting["location"]
                        current_time = meeting["end"]
                    
                    return True
                
                sub_problem.addConstraint(sub_travel_constraint, 
                                        [f"{person}_start" for person in meeting_subset])
                
                sub_solutions = sub_problem.getSolutions()
                if sub_solutions:
                    best_solution = sub_solutions[0]
                    best_meetings = meeting_count
                    break
            
            if best_solution:
                break
        
        if best_solution:
            solution = best_solution
            scheduled_people = meeting_subset if 'meeting_subset' in locals() else person_names
        else:
            # No feasible schedule found
            result = {"itinerary": []}
            print(json.dumps(result, indent=2))
            return
    else:
        # Use the first valid solution
        solution = solutions[0]
        scheduled_people = person_names
    
    # Build itinerary
    itinerary = []
    
    # Create list of scheduled meetings
    meetings = []
    for person in scheduled_people:
        start_time_minutes = solution[f"{person}_start"]
        duration = people[person]["min_duration"]
        end_time_minutes = start_time_minutes + duration
        location = people[person]["location"]
        
        meetings.append({
            "person": person,
            "location": location,
            "start": start_time_minutes,
            "end": end_time_minutes
        })
    
    # Sort meetings by start time
    meetings.sort(key=lambda x: x["start"])
    
    # Add travel from starting point to first meeting
    if meetings:
        first_meeting = meetings[0]
        travel_start = start_time
        travel_end = travel_start + travel_times["The Castro"][first_meeting["location"]]
        
        itinerary.append({
            "action": "travel",
            "from": "The Castro",
            "to": first_meeting["location"],
            "start_time": minutes_to_time(travel_start),
            "end_time": minutes_to_time(travel_end)
        })
    
    # Add meetings and travel between them
    for i, meeting in enumerate(meetings):
        # Add the meeting
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["person"],
            "start_time": minutes_to_time(meeting["start"]),
            "end_time": minutes_to_time(meeting["end"])
        })
        
        # Add travel to next meeting if there is one
        if i < len(meetings) - 1:
            next_meeting = meetings[i + 1]
            travel_start = meeting["end"]
            travel_time = travel_times[meeting["location"]][next_meeting["location"]]
            travel_end = travel_start + travel_time
            
            itinerary.append({
                "action": "travel",
                "from": meeting["location"],
                "to": next_meeting["location"],
                "start_time": minutes_to_time(travel_start),
                "end_time": minutes_to_time(travel_end)
            })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()