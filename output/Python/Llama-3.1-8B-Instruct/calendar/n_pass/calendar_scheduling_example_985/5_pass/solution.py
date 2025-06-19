if (not any((start_time.time() < end_time.time() and end_time.time() < end) or 
            (start_time.time() < end and end_time.time() > start) 
            for start, end in diane_busy)) and \
   (not any((start_time.time() < end_time.time() and end_time.time() < end) or 
            (start_time.time() < end and end_time.time() > start) 
            for start, end in matthew_busy)):
    # Code to be executed if the condition is met