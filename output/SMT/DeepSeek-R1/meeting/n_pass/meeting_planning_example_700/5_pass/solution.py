from z3 import *

def main():
    total_days = 7
    people = ["A", "B", "C", "D", "E", "F", "G"]
    constraints = {
        "A": [0, 1, 2, 3, 4, 5, 6],
        "B": [0, 1, 2, 3, 4, 5, 6],
        "C": [0, 1, 2, 3, 4, 5, 6],
        "D": [0, 1, 2, 3, 4, 5, 6],
        "E": [0, 1, 2, 3, 4, 5, 6],
        "F": [0, 1, 2, 3, 4, 5, 6],
        "G": [0, 1, 2, 3, 4, 5, 6]
    }
    meetings = {
        "M1": ["A", "B", "C"],
        "M2": ["A", "B", "D"],
        "M3": ["A", "C", "E"],
        "M4": ["B", "D", "F"],
        "M5": ["C", "E", "G"],
        "M6": ["D", "F", "G"],
        "M7": ["A", "E", "F"],
        "M8": ["B", "C", "G"],
        "M9": ["A", "D", "G"],
        "M10": ["C", "D", "E"]
    }
    
    # Create meeting day variables
    meeting_days = {m: Int(f"day_{m}") for m in meetings}
    
    # Create solver
    s = Solver()
    s.set("timeout", 300000)  # 5-minute timeout
    
    # Constraint: meeting days must be within valid range
    for m in meetings:
        s.add(meeting_days[m] >= 0, meeting_days[m] < total_days)
    
    # Enforce that no person is double-booked on the same day
    for person in people:
        # Get all meetings this person attends
        persons_meetings = [m for m, attendees in meetings.items() if person in attendees]
        
        # For each pair of meetings this person attends, they must be on different days
        for i in range(len(persons_meetings)):
            for j in range(i+1, len(persons_meetings)):
                m1 = persons_meetings[i]
                m2 = persons_meetings[j]
                s.add(meeting_days[m1] != meeting_days[m2])
    
    # Meetings must be scheduled when all participants are available
    for m, attendees in meetings.items():
        for person in attendees:
            s.add(Or([meeting_days[m] == d for d in constraints[person]]))
    
    # Solve and output
    if s.check() == sat:
        model = s.model()
        for m in meetings:
            day = model.eval(meeting_days[m])
            print(f"{m} is scheduled on day {day}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()