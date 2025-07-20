from z3 import *

def main():
    s = Solver()
    start = Int('start')
    
    # Work hours: 9:00 (0 minutes) to 17:00 (480 minutes). Meeting duration 30 minutes, so start must be <= 450.
    s.add(start >= 0)
    s.add(start <= 450)
    
    # Jacob's busy intervals: [13:30-14:00) -> [270, 300), [14:30-15:00) -> [330, 360)
    jacob_busy = [(270, 300), (330, 360)]
    for a, b in jacob_busy:
        s.add(Or(start + 30 <= a, start >= b))
    
    # Diana's busy intervals: [9:30-10:00) -> [30,60), [11:30-12:00) -> [150,180), [13:00-13:30) -> [240,270), [16:00-16:30) -> [420,450)
    diana_busy = [(30, 60), (150, 180), (240, 270), (420, 450)]
    for a, b in diana_busy:
        s.add(Or(start + 30 <= a, start >= b))
    
    # Adam's busy intervals: [9:30-10:30) -> [30,90), [11:00-12:30) -> [120,210), [15:30-16:00) -> [390,420)
    adam_busy = [(30, 90), (120, 210), (390, 420)]
    for a, b in adam_busy:
        s.add(Or(start + 30 <= a, start >= b))
    
    # Angela's busy intervals: [9:30-10:00) -> [30,60), [10:30-12:00) -> [90,180), [13:00-15:30) -> [240,390), [16:00-16:30) -> [420,450)
    angela_busy = [(30, 60), (90, 180), (240, 390), (420, 450)]
    for a, b in angela_busy:
        s.add(Or(start + 30 <= a, start >= b))
    
    # Dennis's busy intervals: [9:00-9:30) -> [0,30), [10:30-11:30) -> [90,150), [13:00-15:00) -> [240,360), [16:30-17:00) -> [450,480)
    dennis_busy = [(0, 30), (90, 150), (240, 360), (450, 480)]
    for a, b in dennis_busy:
        s.add(Or(start + 30 <= a, start >= b))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        
        # Convert start time from minutes to HH:MM
        total_minutes = start_min
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_str = f"{hours}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_min + 30
        end_hours = 9 + end_minutes // 60
        end_minutes %= 60
        end_str = f"{end_hours}:{end_minutes:02d}"
        
        print(f"Monday, {start_str}, {end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()