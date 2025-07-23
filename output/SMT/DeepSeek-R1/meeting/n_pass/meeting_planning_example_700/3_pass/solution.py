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
    
    meeting_vars = {m: Int(f"day_{m}") for m in meetings}
    s = Optimize()
    s.set("timeout", 300000)

    # Constraint: scheduled meetings must be within valid days
    for meeting in meetings:
        s.add(meeting_vars[meeting] >= 0, meeting_vars[meeting] < total_days)
    
    # Person can attend at most one meeting per day
    for person in people:
        for day in range(total_days):
            meetings_on_day = []
            for meeting, attendees in meetings.items():
                if person in attendees:
                    meetings_on_day.append(meeting_vars[meeting] == day)
            if meetings_on_day:
                s.add(AtMost(*meetings_on_day, 1))
    
    # Meetings must be scheduled when participants are available
    for person in people:
        available_days = constraints[person]
        for meeting, attendees in meetings.items():
            if person in attendees:
                s.add(Or([meeting_vars[meeting] == d for d in available_days]))
    
    # Check satisfiability without optimization
    if s.check() == sat:
        model = s.model()
        for meeting in meetings:
            day = model.eval(meeting_vars[meeting])
            print(f"{meeting} is scheduled on day {day}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()