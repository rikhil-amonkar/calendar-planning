from z3 import *
import json

def minutes_to_time_str(m):
    # Convert integer minutes after midnight to a string "H:MM" in 24-hour format.
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Create an Optimize instance
    opt = Optimize()

    # Declare integer variables representing meeting start times (in minutes after midnight)
    # Timothy at Alamo Square: available from 12:00 (720) to 16:15 (975) with 105 minutes meeting required.
    t_start = Int("t_start")
    # Joseph at Russian Hill: available from 16:45 (1005) to 21:30 (1290) with 60 minutes meeting required.
    j_start = Int("j_start")
    # Mark at Presidio: available from 18:45 (1125) to 21:00 (1260) with 60 minutes meeting required.
    m_start = Int("m_start")
    
    # Boolean variable to select the order of Mark and Joseph after Timothy.
    # If order_flag is True, the order is: Timothy -> Joseph -> Mark.
    # If order_flag is False, the order is: Timothy -> Mark -> Joseph.
    order_flag = Bool("order_flag")
    
    # Define meeting durations and computed end-times.
    t_duration = 105
    j_duration = 60
    m_duration = 60

    t_end = t_start + t_duration
    j_end = j_start + j_duration
    m_end = m_start + m_duration

    # Constraint: You arrive at Golden Gate Park at 9:00 (540) and travel to Alamo Square takes 10 minutes.
    # Since Timothy is only available from 12:00 (720), we require:
    opt.add(t_start >= 720)
    opt.add(t_end <= 975)  # Timothy must finish by 16:15 (975)

    # Define constraints for the two possible meeting orders

    # Order 1: Timothy -> Joseph -> Mark
    # Timothy meeting is at Alamo Square.
    # Travel from Alamo Square to Russian Hill takes 13 minutes.
    # Joseph is available from 16:45 (1005) to 21:30 (1290).
    # Travel from Russian Hill to Presidio takes 14 minutes.
    # Mark is available from 18:45 (1125) to 21:00 (1260).
    order_true = And(
        j_start >= t_end + 13,   # travel time from Alamo Square to Russian Hill
        j_start >= 1005,         # Joseph's availability start
        j_end <= 1290,           # Joseph's availability end
        m_start >= j_end + 14,   # travel time from Russian Hill to Presidio
        m_start >= 1125,         # Mark's availability start
        m_end <= 1260            # Mark's availability end
    )

    # Order 2: Timothy -> Mark -> Joseph
    # Travel from Alamo Square to Presidio takes 18 minutes.
    # Then travel from Presidio to Russian Hill takes 14 minutes.
    order_false = And(
        m_start >= t_end + 18,   # travel time from Alamo Square to Presidio
        m_start >= 1125,         # Mark's availability start
        m_end <= 1260,           # Mark's availability end
        j_start >= m_end + 14,   # travel time from Presidio to Russian Hill
        j_start >= 1005,         # Joseph's availability start
        j_end <= 1290            # Joseph's availability end
    )

    # Add a constraint that enforces either one of the orders according to order_flag.
    opt.add(Or(
        And(order_flag, order_true),
        And(Not(order_flag), order_false)
    ))

    # Additional domain constraint: Ensure Timothy's meeting start is such that t_end <= 975.
    opt.add(t_start <= 975 - t_duration)

    # Objective: minimize the finish time of the final meeting.
    # Final finish time is m_end if order_flag True (Timothy -> Joseph -> Mark)
    # or j_end if order_flag is False (Timothy -> Mark -> Joseph).
    final_finish = If(order_flag, m_end, j_end)
    opt.minimize(final_finish)

    # Check and obtain a model
    if opt.check() == sat:
        sol = opt.model()
        t_start_val = sol[t_start].as_long()
        j_start_val = sol[j_start].as_long()
        m_start_val = sol[m_start].as_long()
        order_val = sol[order_flag]
        
        itinerary = []
        # Timothy meeting at Alamo Square is always first.
        itinerary.append({
            "action": "meet",
            "location": "Alamo Square",
            "person": "Timothy",
            "start_time": minutes_to_time_str(t_start_val),
            "end_time": minutes_to_time_str(t_start_val + t_duration)
        })

        if is_true(order_val):
            # Order: Timothy -> Joseph -> Mark
            itinerary.append({
                "action": "meet",
                "location": "Russian Hill",
                "person": "Joseph",
                "start_time": minutes_to_time_str(j_start_val),
                "end_time": minutes_to_time_str(j_start_val + j_duration)
            })
            itinerary.append({
                "action": "meet",
                "location": "Presidio",
                "person": "Mark",
                "start_time": minutes_to_time_str(m_start_val),
                "end_time": minutes_to_time_str(m_start_val + m_duration)
            })
        else:
            # Order: Timothy -> Mark -> Joseph
            itinerary.append({
                "action": "meet",
                "location": "Presidio",
                "person": "Mark",
                "start_time": minutes_to_time_str(m_start_val),
                "end_time": minutes_to_time_str(m_start_val + m_duration)
            })
            itinerary.append({
                "action": "meet",
                "location": "Russian Hill",
                "person": "Joseph",
                "start_time": minutes_to_time_str(j_start_val),
                "end_time": minutes_to_time_str(j_start_val + j_duration)
            })
        
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        # If no schedule could be found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()