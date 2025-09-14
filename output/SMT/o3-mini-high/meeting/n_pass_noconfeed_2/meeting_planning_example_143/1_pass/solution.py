from z3 import *
import json

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Base times (in minutes from midnight)
    NB_arrival = 9 * 60  # 9:00 AM => 540

    # Friends' availability windows (in minutes from midnight)
    # Mark is available at Embarcadero from 13:00 (780) to 17:45 (1065)
    mark_start_avail = 13 * 60      # 780 minutes
    mark_end_avail = 17 * 60 + 45     # 1065 minutes
    mark_min_meeting = 120          # Minimum meeting duration in minutes

    # Karen is available at Pacific Heights from 18:45 (1125) to 20:15 (1215)
    karen_start_avail = 18 * 60 + 45  # 1125 minutes
    karen_end_avail = 20 * 60 + 15    # 1215 minutes
    karen_min_meeting = 90          # Minimum meeting duration in minutes

    # Travel times (in minutes)
    travel_NB_to_PH = 8     # North Beach -> Pacific Heights
    travel_NB_to_EB = 6     # North Beach -> Embarcadero
    travel_PH_to_NB = 9     # Pacific Heights -> North Beach
    travel_PH_to_EB = 10    # Pacific Heights -> Embarcadero
    travel_EB_to_NB = 5     # Embarcadero -> North Beach
    travel_EB_to_PH = 11    # Embarcadero -> Pacific Heights

    # Create an Optimize() solver instance
    opt = Optimize()

    # Decision booleans: whether to schedule a meeting with each friend.
    markScheduled = Bool('markScheduled')
    karenScheduled = Bool('karenScheduled')

    # Variables for meeting times (minutes from midnight)
    m_start = Int('m_start')
    m_end = Int('m_end')
    k_start = Int('k_start')
    k_end = Int('k_end')

    # Constraints for meeting Mark (at Embarcadero) if scheduled.
    opt.add(Implies(markScheduled, m_start >= mark_start_avail))
    opt.add(Implies(markScheduled, m_end <= mark_end_avail))
    opt.add(Implies(markScheduled, m_end - m_start >= mark_min_meeting))
    # Ensure you have traveled from North Beach to Embarcadero.
    opt.add(Implies(markScheduled, m_start >= NB_arrival + travel_NB_to_EB))

    # Constraints for meeting Karen (at Pacific Heights) if scheduled.
    opt.add(Implies(karenScheduled, k_start == karen_start_avail))
    opt.add(Implies(karenScheduled, k_end == karen_end_avail))
    opt.add(Implies(karenScheduled, k_end - k_start >= karen_min_meeting))
    # Ensure travel from North Beach to Pacific Heights is feasible.
    opt.add(Implies(karenScheduled, k_start >= NB_arrival + travel_NB_to_PH))

    # If both meetings are scheduled, enforce travel from Embarcadero to Pacific Heights.
    opt.add(Implies(And(markScheduled, karenScheduled), m_end + travel_EB_to_PH <= k_start))

    # Our primary goal is to maximize the number of meetings.
    friend_count = If(markScheduled, 1, 0) + If(karenScheduled, 1, 0)
    opt.maximize(friend_count)

    # Secondary objectives: if meeting Mark, start as early as possible and use the minimum duration.
    opt.minimize(If(markScheduled, m_start, 0))
    opt.minimize(If(markScheduled, m_end - m_start, 0))
    
    # Check for an optimal schedule.
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        
        if model.evaluate(markScheduled):
            m_start_val = model.evaluate(m_start).as_long()
            m_end_val = model.evaluate(m_end).as_long()
            itinerary.append({
                "action": "meet",
                "location": "Embarcadero",
                "person": "Mark",
                "start_time": minutes_to_time(m_start_val),
                "end_time": minutes_to_time(m_end_val)
            })

        if model.evaluate(karenScheduled):
            k_start_val = model.evaluate(k_start).as_long()
            k_end_val = model.evaluate(k_end).as_long()
            itinerary.append({
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Karen",
                "start_time": minutes_to_time(k_start_val),
                "end_time": minutes_to_time(k_end_val)
            })

        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()