baseruby="ruby --disable=gems"
ruby="${RUBY-$baseruby}"
"eval" "{" \
"`expr \"$ruby\" : echo > /dev/null || echo exec`" \
"$ruby" '-r"`expr \"$0\" : / > /dev/null || pwd`/${0#/}" "$@";' \
"}" || "exit" "$?"
ruby=ruby
class Object
  remove_const :CROSS_COMPILING if defined?(CROSS_COMPILING)
  CROSS_COMPILING = RUBY_PLATFORM
  remove_const :RUBY_PLATFORM
  remove_const :RUBY_VERSION
  remove_const :RUBY_RELEASE_DATE
  remove_const :RUBY_DESCRIPTION if defined?(RUBY_DESCRIPTION)
  RUBY_PLATFORM = "x86_64-darwin14"
  RUBY_VERSION = "2.2.2"
  RUBY_RELEASE_DATE = "@RUBY_RELEASE_DATE@"
  RUBY_DESCRIPTION = "ruby #{RUBY_VERSION} (#{RUBY_RELEASE_DATE}) [#{RUBY_PLATFORM}]"
end
builddir = File.dirname(__FILE__)
top_srcdir = "/Users/Mike/RubyCore"
if /mingw/ =~ RUBY_PLATFORM
  # convert MSYS path to Windows path
  top_srcdir.sub!(/\A\/([a-z])\//, '\\1:/')
end
$:.unshift(File.expand_path(builddir))
fake = File.join(top_srcdir, "tool/fake.rb")
eval(File.read(fake), nil, fake)
