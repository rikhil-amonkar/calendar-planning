from z3 import *
import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Create an optimizer instance
    opt = Optimize()

    # Define integer variables for meeting start and end times (in minutes after midnight)
    s_start = Int("s_start")
    s_end   = Int("s_end")
    j_start = Int("j_start")
    j_end   = Int("j_end")
    
    # Define Boolean flags to indicate whether we meet each friend.
    meet_S = Bool("meet_S")  # meeting Stephanie at Financial District
    meet_J = Bool("meet_J")  # meeting John at Alamo Square

    # Constants for starting time and travel times (all times in minutes)
    arrival_Embarcadero = 9 * 60           # 9:00 -> 540
    t_E_to_F = 5                         # Embarcadero to Financial District
    t_E_to_A = 19                        # Embarcadero to Alamo Square
    t_F_to_A = 17                        # Financial District to Alamo Square

    # Friends' available time windows (in minutes after midnight)
    steph_avail_start = 8 * 60 + 15        # 8:15 -> 495
    steph_avail_end   = 11 * 60 + 30         # 11:30 -> 690
    john_avail_start  = 10 * 60 + 15         # 10:15 -> 615
    john_avail_end    = 20 * 60 + 45         # 20:45 -> 1245

    # Minimum meeting durations (in minutes)
    min_dur_S = 90
    min_dur_J = 30

    # ---------------------
    # Constraints for meeting Stephanie (at Financial District)
    # If meeting Stephanie, we must leave Embarcadero at 9:00 and travel t_E_to_F minutes.
    opt.add(Implies(meet_S, s_start >= arrival_Embarcadero + t_E_to_F))
    # Also must honor her availability window.
    opt.add(Implies(meet_S, s_start >= steph_avail_start))
    opt.add(Implies(meet_S, s_end   <= steph_avail_end))
    # Must meet for at least 90 minutes.
    opt.add(Implies(meet_S, s_end - s_start >= min_dur_S))
    # Moreover, to have room for a 90-minute meeting before her window closes:
    opt.add(Implies(meet_S, s_start <= steph_avail_end - min_dur_S))
    # If not meeting Stephanie, fix times to 0.
    opt.add(Implies(Not(meet_S), s_start == 0))
    opt.add(Implies(Not(meet_S), s_end == 0))
    
    # ---------------------
    # Constraints for meeting John (at Alamo Square)
    opt.add(Implies(meet_J, j_start >= john_avail_start))
    opt.add(Implies(meet_J, j_end   <= john_avail_end))
    opt.add(Implies(meet_J, j_end - j_start >= min_dur_J))
    # Ensure John’s meeting can start early enough:
    opt.add(Implies(meet_J, j_start <= john_avail_end - min_dur_J))
    # If not meeting John, fix times to 0.
    opt.add(Implies(Not(meet_J), j_start == 0))
    opt.add(Implies(Not(meet_J), j_end == 0))
    
    # ---------------------
    # Travel constraint to John's meeting depends on whether we met Stephanie.
    # If we met Stephanie, then after finishing at Financial District we travel t_F_to_A minutes.
    opt.add(Implies(And(meet_J, meet_S), j_start >= s_end + t_F_to_A))
    # Otherwise, if not meeting Stephanie, we travel directly from Embarcadero, with t_E_to_A minutes.
    opt.add(Implies(And(meet_J, Not(meet_S)), j_start >= arrival_Embarcadero + t_E_to_A))
    
    # Ensure non-negative times.
    opt.add(s_start >= 0, s_end >= 0, j_start >= 0, j_end >= 0)
    
    # ---------------------
    # Define an objective: We want to meet as many friends as possible.
    # In our context, "optimal" means maximizing the total number of meetings and, if equal,
    # finishing as early as possible.
    meeting_count = If(meet_S, 1, 0) + If(meet_J, 1, 0)
    finish_time = If(meet_J, j_end, If(meet_S, s_end, arrival_Embarcadero))
    
    h1 = opt.maximize(meeting_count)
    h2 = opt.minimize(finish_time)
    
    # ---------------------
    # Check for satisfiability and extract the schedule.
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        if model.eval(meet_S):
            s_start_val = model.eval(s_start).as_long()
            s_end_val   = model.eval(s_end).as_long()
            itinerary.append({
                "action": "meet",
                "location": "Financial District",
                "person": "Stephanie",
                "start_time": format_time(s_start_val),
                "end_time": format_time(s_end_val)
            })
        if model.eval(meet_J):
            j_start_val = model.eval(j_start).as_long()
            j_end_val   = model.eval(j_end).as_long()
            itinerary.append({
                "action": "meet",
                "location": "Alamo Square",
                "person": "John",
                "start_time": format_time(j_start_val),
                "end_time": format_time(j_end_val)
            })
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()