from z3 import *

def main():
    # Define the variables
    day = Int('day')
    slot = Int('slot')
    
    # Busy slots for Monday
    arthur_busy_mon = [4, 9, 12]
    michael_busy_mon = [0, 1, 2, 3, 4, 5, 7, 10, 12, 13, 14, 15]
    
    # Busy slots for Wednesday
    arthur_busy_wed = [2, 4, 6, 10, 14]
    michael_busy_wed = [2, 3, 4, 5, 6, 8]
    
    s = Optimize()
    
    # Day must be Monday (0) or Wednesday (2)
    s.add(Or(day == 0, day == 2))
    # Slot must be between 0 and 15 inclusive
    s.add(slot >= 0, slot <= 15)
    
    # Helper function to check if a slot is not in a busy list
    def not_in_busy(slot_var, busy_list):
        return And([slot_var != busy for busy in busy_list])
    
    # Condition for Monday: slot not in Arthur's or Michael's busy list
    mon_cond = And(not_in_busy(slot, arthur_busy_mon), 
                   not_in_busy(slot, michael_busy_mon))
    # Condition for Wednesday: slot not in Arthur's or Michael's busy list
    wed_cond = And(not_in_busy(slot, arthur_busy_wed), 
                   not_in_busy(slot, michael_busy_wed))
    
    # Add constraints based on the selected day
    s.add(If(day == 0, mon_cond, wed_cond))
    
    # Minimize the score: day * 100 + slot to prioritize earlier day and slot
    score = day * 100 + slot
    s.minimize(score)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        d = m[day].as_long()
        sl = m[slot].as_long()
        
        # Convert slot to start time in minutes
        total_minutes = 9 * 60 + sl * 30
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = total_minutes + 30
        end_hours = end_minutes // 60
        end_minutes %= 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Map day code to day name
        day_name = "Monday" if d == 0 else "Wednesday"
        
        # Print the solution
        print(f"Day: {day_name}")
        print(f"Start: {start_time}")
        print(f"End: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()