import json
from z3 import *

def minutes_to_time_str(minutes_since_9):
    # 9:00 AM is our baseline (9*60 = 540 minutes from midnight)
    total = 540 + minutes_since_9
    hour = total // 60
    minute = total % 60
    return f"{hour}:{minute:02d}"

def main():
    # Create an optimizer instance
    opt = Optimize()

    # Boolean decision variables: whether to meet each friend
    x_emily = Bool("x_emily")
    x_barbara = Bool("x_barbara")
    x_william = Bool("x_william")

    # Time variables (in minutes since 9:00 AM)
    # For each meeting we assign a start time and a meeting duration.
    E_start = Int("E_start")
    d_e = Int("d_e")
    B_start = Int("B_start")
    d_b = Int("d_b")
    W_start = Int("W_start")
    d_w = Int("d_w")

    # Define end times as expressions
    E_end = E_start + d_e
    B_end = B_start + d_b
    W_end = W_start + d_w

    # If a meeting is not scheduled, fix its time/duration to 0.
    opt.add(Implies(Not(x_emily), E_start == 0))
    opt.add(Implies(Not(x_emily), d_e == 0))
    opt.add(Implies(Not(x_barbara), B_start == 0))
    opt.add(Implies(Not(x_barbara), d_b == 0))
    opt.add(Implies(Not(x_william), W_start == 0))
    opt.add(Implies(Not(x_william), d_w == 0))

    # ---------------------------
    # Meeting constraints:
    #
    # You start at The Castro at 9:00, so travel to the meeting location must be accounted for.
    #
    # Emily will be at Alamo Square from 11:45 (165 minutes since 9:00) to 15:15 (375 minutes).
    # Minimum meeting duration with Emily: 105 minutes.
    opt.add(Implies(x_emily, And(
        E_start >= 165,            # Must not start before her available time
        E_start <= 270,            # To allow at least 105 minutes before 15:15 (375 - 105 = 270)
        d_e >= 105,
        E_end <= 375
    )))

    # Barbara will be at Union Square from 16:45 (465 minutes) to 18:15 (555 minutes).
    # Minimum meeting duration with Barbara: 60 minutes.
    opt.add(Implies(x_barbara, And(
        B_start >= 465,
        B_start <= 495,           # To allow at least 60 minutes before 555 (555 - 60 = 495)
        d_b >= 60,
        B_end <= 555
    )))

    # William will be at Chinatown from 17:15 (495 minutes) to 19:00 (600 minutes).
    # Minimum meeting duration: 105 minutes. Since 600-495 = 105, his meeting fills the window.
    opt.add(Implies(x_william, And(
        W_start == 495,
        d_w == 105
    )))

    # ---------------------------
    # Travel times (in minutes)
    # From The Castro (starting point) to:
    #   - Alamo Square: 8 minutes (but Emily's window forces 11:45 as earliest meeting time)
    #   - Union Square: 19 minutes (Barbara's available time starts at 16:45)
    #   - Chinatown: 20 minutes (William's available time starts at 17:15)
    #
    # Travel times between meeting locations:
    #   - Alamo Square to Union Square: 14 minutes
    #   - Alamo Square to Chinatown: 16 minutes
    #   - Union Square to Chinatown: 7 minutes and vice versa.
    # Ordering constraints if two meetings are scheduled:
    opt.add(Implies(And(x_emily, x_barbara), E_end + 14 <= B_start))
    opt.add(Implies(And(x_emily, x_william), E_end + 16 <= W_start))
    # For Barbara and William, neither order can actually work because of their tight windows.
    opt.add(Implies(And(x_barbara, x_william), 
                    Or(B_end + 7 <= W_start, W_end + 7 <= B_start)))
    
    # ---------------------------
    # Objective:
    # We'll maximize the number of meetings (friend count) first.
    # In the event of a tie, we prefer a schedule that maximizes total meeting duration.
    friend_count = If(x_emily, 1, 0) + If(x_barbara, 1, 0) + If(x_william, 1, 0)
    total_duration = If(x_emily, d_e, 0) + If(x_barbara, d_b, 0) + If(x_william, d_w, 0)
    # Weight friend count heavily so that two meetings beat one, and three (if possible) would be best.
    objective = 10000 * friend_count + total_duration
    opt.maximize(objective)

    # ---------------------------
    # Check satisfiability and extract solution
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        meetings = []
        
        if is_true(model.evaluate(x_emily)):
            e_start_val = model.evaluate(E_start).as_long()
            e_end_val = model.evaluate(E_end).as_long()
            meetings.append((e_start_val, {
                "action": "meet",
                "location": "Alamo Square",
                "person": "Emily",
                "start_time": minutes_to_time_str(e_start_val),
                "end_time": minutes_to_time_str(e_end_val)
            }))
        
        if is_true(model.evaluate(x_barbara)):
            b_start_val = model.evaluate(B_start).as_long()
            b_end_val = model.evaluate(B_end).as_long()
            meetings.append((b_start_val, {
                "action": "meet",
                "location": "Union Square",
                "person": "Barbara",
                "start_time": minutes_to_time_str(b_start_val),
                "end_time": minutes_to_time_str(b_end_val)
            }))
        
        if is_true(model.evaluate(x_william)):
            w_start_val = model.evaluate(W_start).as_long()
            w_end_val = model.evaluate(W_end).as_long()
            meetings.append((w_start_val, {
                "action": "meet",
                "location": "Chinatown",
                "person": "William",
                "start_time": minutes_to_time_str(w_start_val),
                "end_time": minutes_to_time_str(w_end_val)
            }))
        
        # Sort the meetings in chronological order
        meetings.sort(key=lambda x: x[0])
        itinerary = [m[1] for m in meetings]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # If unsat, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()