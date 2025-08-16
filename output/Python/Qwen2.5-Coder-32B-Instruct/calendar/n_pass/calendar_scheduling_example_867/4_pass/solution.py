excluded = any(start <= current_time_minutes < end or start < meeting_end_minutes <= end 
               for start, end in [(ex, ex + 1) for ex in excluded_times.get(day, [])])