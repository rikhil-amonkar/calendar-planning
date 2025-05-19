import tiktoken
# Define the model (e.g., "gpt-3.5-turbo" or "gpt-4")
model_name = "deepseek-chat" # this doesn't matter
# Initialize the encoder for the specific model
encoding = tiktoken.encoding_for_model(model_name)
# Document to be tokenized
document = """



"""
# Count the tokens
tokens = encoding.encode(document)
token_count = len(tokens)
print(f"Number of tokens: {token_count}")