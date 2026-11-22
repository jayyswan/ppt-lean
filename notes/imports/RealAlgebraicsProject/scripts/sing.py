import subprocess, random
def run(script, timeout=600):
    r = subprocess.run(['Singular','-q','--no-warn'], input=script+"\nquit;\n", capture_output=True, text=True, timeout=timeout)
    return r.stdout
