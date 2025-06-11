from z3 import *

def min_to_time(m):
    hour = 9 + m // 60
    mins = m % 60
    if hour < 12:
        return f"{hour}:{mins:02d} AM"
    elif hour == 12:
        return f"12:{mins:02d} PM"
    else:
        hour -= 12
        return f"{hour}:{mins:02d} PM"

def main():
    s = Optimize()
    t0 = Int('t0')
    s.add(t0 >= 0)
    
    meeting_Jason = 90
    meeting_Kenneth = 45
    
    arrive_PR = t0 + 11
    start_Jason = If(arrive_PR >= 60, arrive_PR, 60)
    end_Jason = start_Jason + meeting_Jason
    s.add(end_Jason <= 435)
    
    arrive_MD = end_Jason + 10
    start_Kenneth = If(arrive_MD >= 390, arrive_MD, 390)
    end_Kenneth = start_Kenneth + meeting_Kenneth
    s.add(end_Kenneth <= 465)
    
    wait_PR = If(arrive_PR < 60, 60 - arrive_PR, 0)
    wait_MD = If(arrive_MD < 390, 390 - arrive_MD, 0)
    total_wait = wait_PR + wait_MD
    
    s.minimize(total_wait)
    
    if s.check() == sat:
        m = s.model()
        t0_val = m[t0].as_long()
        arrive_PR_val = t0_val + 11
        start_Jason_val = arrive_PR_val if arrive_PR_val >= 60 else 60
        end_Jason_val = start_Jason_val + 90
        arrive_MD_val = end_Jason_val + 10
        start_Kenneth_val = arrive_MD_val if arrive_MD_val >= 390 else 390
        end_Kenneth_val = start_Kenneth_val + 45
        wait_PR_val = 60 - arrive_PR_val if arrive_PR_val < 60 else 0
        wait_MD_val = 390 - arrive_MD_val if arrive_MD_val < 390 else 0
        total_wait_val = wait_PR_val + wait_MD_val
        
        print("SOLUTION:")
        print(f"Depart Pacific Heights at: {min_to_time(t0_val)}")
        print(f"Arrive Presidio at: {min_to_time(arrive_PR_val)}")
        print(f"Meet Jason from: {min_to_time(start_Jason_val)} to {min_to_time(end_Jason_val)}")
        print(f"Depart Presidio at: {min_to_time(end_Jason_val)}")
        print(f"Arrive Marina District at: {min_to_time(arrive_MD_val)}")
        print(f"Meet Kenneth from: {min_to_time(start_Kenneth_val)} to {min_to_time(end_Kenneth_val)}")
        print(f"Total waiting time: {total_wait_val} minutes")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()